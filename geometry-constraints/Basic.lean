import Mathlib
open scoped RealInnerProductSpace
set_option linter.style.longLine false

/- A point in the Euclidean plane -/
abbrev Point : Type := EuclideanSpace ℝ (Fin 2)

/-The displacement vector from point a to point b.-/
noncomputable def Vec (a b : Point) : Point := b - a

/-The statement that the distance between points a and b = d.-/
def Distance (a b : Point) (d : ℝ) : Prop := dist a b = d

/-The statement that the segment from c to d is a scalar multiple of the segment from a to b.-/
def Parallel (a b c d : Point) : Prop :=
  ∃ t : ℝ, Vec c d = t • Vec a b

/-The statement that the segments ab and cd meet at a right angle-/
def Perpendicular (a b c d : Point) : Prop :=
  ⟪Vec a b, Vec c d⟫ = 0

/-Constructs a concrete point in the plane from its two real coordinates-/
noncomputable def pt (x y : ℝ) : Point :=
  (WithLp.equiv 2 (Fin 2 → ℝ)).symm ![x, y]


/- symmetric properties  -/

/-Demonstrates that perpendicularity is symmetric in its two segments, without giving it a name.-/
example (a b c d : Point) :
    Perpendicular a b c d ↔ Perpendicular c d a b := by
  unfold Perpendicular
  constructor
  · intro h; rw [← h]; exact real_inner_comm _ _
  · intro h; rw [← h]; exact real_inner_comm _ _

/-Verifies the concrete instance that the segment along the x-axis from (1,0)
to the origin is perpendicular to the segment along the y-axis from the origin to (0,1).-/
example : Perpendicular (pt 1 0) (pt 0 0) (pt 0 0) (pt 0 1) := by
  unfold Perpendicular Vec pt
  simp [PiLp.inner_apply, Fin.sum_univ_two, WithLp.equiv]

/-The distance between two points doesn't depend on which one you measure from-/
theorem Distance.symm (a b : Point) (d : ℝ) :
    Distance a b d ↔ Distance b a d := by
  unfold Distance
  rw [dist_comm]

/-If segment ab is perpendicular to segment cd, then segment cd is also perpendicular to segment ab.-/
theorem Perpendicular.symm (a b c d : Point) :
    Perpendicular a b c d ↔ Perpendicular c d a b := by
  unfold Perpendicular
  constructor
  · intro h; rw [← h]; exact real_inner_comm _ _
  · intro h; rw [← h]; exact real_inner_comm _ _

/-If segment cd is a nonzero scalar multiple of segment ab, then ab is also a scalar multiple of cd -/
theorem Parallel.symm_of_ne_zero (a b c d : Point) (t : ℝ) (ht : t ≠ 0)
    (h : Vec c d = t • Vec a b) :
    Parallel c d a b := by
  refine ⟨1 / t, ?_⟩
  rw [h, smul_smul, one_div, inv_mul_cancel₀ ht, one_smul]

/- right angle bridge -/

/-
Two segments are perpendicular in the definition exactly when the standard geometric
angle between their direction vectors equals π/2
bridging the inner-product-based definition to Mathlib's notion of angle.
-/
theorem Perpendicular.iff_angle_eq_pi_div_two (a b c d : Point) :
    Perpendicular a b c d ↔
      InnerProductGeometry.angle (Vec a b) (Vec c d) = Real.pi / 2 := by
  unfold Perpendicular
  exact InnerProductGeometry.inner_eq_zero_iff_angle_eq_pi_div_two (Vec a b) (Vec c d)

/- distance characterizes a sphere -/

/-- A point p is at distance r from center iff it lies on the sphere
of radius r centered at center. -/
theorem Distance.iff_mem_sphere (center p : Point) (r : ℝ) :
    Distance center p r ↔ p ∈ Metric.sphere center r := by
  unfold Distance
  rw [Metric.mem_sphere, dist_comm]

/-- Given a right angle at b, if the legs a`
and bc have lengths p and q respectively, the hypotenuse a` has
length √(p² + q²). Nonnegativity of p and q is implied by
Distance a b p where dist is always nonnegative and not needed
as a hypothesis. -/
theorem pythagorean (a b c : Point) (p q : ℝ)
    (hperp : Perpendicular a b b c)
    (hab : Distance a b p)
    (hbc : Distance b c q) :
    Distance a c (Real.sqrt (p^2 + q^2)) := by
  unfold Distance at hab hbc ⊢
  unfold Perpendicular at hperp
  rw [dist_eq_norm] at hab hbc ⊢
  have hsum : a - c = -(Vec a b + Vec b c) := by
    unfold Vec; abel
  rw [hsum, norm_neg]
  have hsq : ‖Vec a b + Vec b c‖^2 = p^2 + q^2 := by
    rw [norm_add_sq_real, hperp]
    have h1 : ‖Vec a b‖ = p := by
      rw [← hab]; unfold Vec; rw [norm_sub_rev]
    have h2 : ‖Vec b c‖ = q := by
      rw [← hbc]; unfold Vec; rw [norm_sub_rev]
    rw [h1, h2]
    ring
  have hnn : (0 : ℝ) ≤ ‖Vec a b + Vec b c‖ := norm_nonneg _
  rw [show ‖Vec a b + Vec b c‖
        = Real.sqrt (‖Vec a b + Vec b c‖^2) from (Real.sqrt_sq hnn).symm,
      hsq]
