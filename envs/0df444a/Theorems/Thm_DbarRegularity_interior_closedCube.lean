-- Prove2me | Theorems.Thm_DbarRegularity_interior_closedCube
-- name    : DbarRegularity.interior_closedCube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:29:04.632082+00:00
-- url     : https://prove2.me/theorems/97a6d559-9b11-439b-a70a-f4341df4e0a4
-- title:
--   Interior of a closed cube in ℝ^d
-- statement:
--   For $a\in\mathbb{R}^d$ and $s\in\mathbb{R}$, the interior of the closed cube $Q(a,s)=\{x:\ a_i\le x_i\le a_i+s\ \forall i\}$ is the open cube
--   $$\operatorname{int} Q(a,s)=\{x\in\mathbb{R}^d:\ a_i<x_i<a_i+s\ \text{for all } i\}.$$
--
--   It describes exactly when two closed cubes have disjoint interiors.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with its Euclidean topology, and `x i` is the $i$-th coordinate. No restriction on $d$ or $s$.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory

/-- The interior of the closed cube `∏ᵢ [aᵢ, aᵢ + s]` in `ℝ^d` is the open cube
`∏ᵢ (aᵢ, aᵢ + s)`. -/
theorem interior_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    interior (closedCube a s) = {x | ∀ i, a i < x i ∧ x i < a i + s} := by sorry

end DbarRegularity
