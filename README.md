# Geometry Constraints

A formalization in Lean 4 of a basic 2D geometric constraint system —
the same kind of system that underlies real CAD and geometric solver
code. Built on [Mathlib](https://leanprover-community.github.io/mathlib4_docs/).

## What's here

Three primitive constraints between points in the Euclidean plane:

- **Distance** — a metric constraint
- **Parallel** — a direction constraint
- **Perpendicular** — an inner-product constraint

And six theorems about them:

| Theorem | Statement |
|---|---|
| `Distance.symm` | Distance is symmetric in its arguments |
| `Perpendicular.symm` | Perpendicularity is symmetric between the two segments |
| `Parallel.symm_of_ne_zero` | Parallelism is symmetric when the scaling factor is nonzero |
| `Perpendicular.iff_angle_eq_pi_div_two` | Perpendicular ↔ angle equals π/2 |
| `Distance.iff_mem_sphere` | Distance characterizes the sphere |
| `pythagorean` | The Pythagorean theorem for right triangles |

See `blueprint.md` for the full mathematical
description and discussion of design choices.

## Building

Requires [elan](https://github.com/leanprover/elan) (which installs Lean and Lake).

lake exe cache get
lake build

The `cache get` step downloads precompiled Mathlib artifacts; without it, the first build takes hours.

## File layout
- `GeometryConstraints/Basic.lean` — all definitions and theorems

