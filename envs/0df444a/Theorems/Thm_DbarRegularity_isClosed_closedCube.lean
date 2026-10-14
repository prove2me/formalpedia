-- Prove2me | Theorems.Thm_DbarRegularity_isClosed_closedCube
-- name    : DbarRegularity.isClosed_closedCube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:45:57.897393+00:00
-- url     : https://prove2.me/theorems/7a42f168-30dc-4955-a8b2-f1088575729a
-- title:
--   Closed cubes in ℝ^d are closed
-- statement:
--   For every $a\in\mathbb{R}^d$ and $s\in\mathbb{R}$, the closed cube
--   $$Q(a,s)=\{x\in\mathbb{R}^d:\ a_i\le x_i\le a_i+s\ \text{for all } i\}$$
--   is a closed subset of $\mathbb{R}^d$.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with its Euclidean topology.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

/-- The closed cube `∏ᵢ [aᵢ, aᵢ + s]` is a closed subset of `ℝ^d`. -/
theorem isClosed_closedCube {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    IsClosed (closedCube a s) := by sorry

end DbarRegularity
