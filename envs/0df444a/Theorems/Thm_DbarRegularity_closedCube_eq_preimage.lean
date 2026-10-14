-- Prove2me | Theorems.Thm_DbarRegularity_closedCube_eq_preimage
-- name    : DbarRegularity.closedCube_eq_preimage
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:45:56.582977+00:00
-- url     : https://prove2.me/theorems/c2d2ab9b-7dd4-4d60-a0b6-6fb93d777a2c
-- title:
--   Closed cubes in ℝ^d as preimages of order intervals
-- statement:
--   For $a\in\mathbb{R}^d$ and $s\in\mathbb{R}$, the closed cube $Q(a,s)=\{x:\ a_i\le x_i\le a_i+s\ \forall i\}$ satisfies
--   $$Q(a,s)=\pi^{-1}\big([a,\,a+s\mathbf 1]\big),$$
--   where $\pi:\mathbb{R}^d\to\mathbb{R}^{\{1,\dots,d\}}$ forgets the Euclidean structure and $[a,a+s\mathbf 1]$ is the order interval for the coordinatewise order on functions $\{1,\dots,d\}\to\mathbb{R}$.
--
--   **Formalization Note.** `closedCube a s` comes from `Definitions.Def_DbarRegularity_Setting`; $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)`, $\pi$ is `WithLp.ofLp`, and the order interval is `Set.Icc (fun i => a i) (fun i => a i + s)` in `Fin d → ℝ`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open Set

/-- The closed cube `∏ᵢ [aᵢ, aᵢ + s]` in `ℝ^d` is the preimage, under the coordinate map
`EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)`, of the order interval `[a, a + s]` of `Fin d → ℝ`. -/
theorem closedCube_eq_preimage {d : ℕ} (a : EuclideanSpace ℝ (Fin d)) (s : ℝ) :
    closedCube a s = (WithLp.ofLp : EuclideanSpace ℝ (Fin d) → (Fin d → ℝ)) ⁻¹'
      Icc (fun i => a i) (fun i => a i + s) := by sorry

end DbarRegularity
