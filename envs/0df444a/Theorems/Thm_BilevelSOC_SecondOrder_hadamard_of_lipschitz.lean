-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_hadamard_of_lipschitz
-- name    : BilevelSOC.SecondOrder.hadamard_of_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:01.104797+00:00
-- url     : https://prove2.me/theorems/e276bab2-e669-41f6-bfa0-f081ba3fcf6b
-- title:
--   §2.3 — local Lipschitz continuity upgrades directional to Hadamard derivatives
-- statement:
--   Let $\theta$ be locally Lipschitz at $x$ and directionally differentiable there in every direction. Its Hadamard directional derivatives then exist and satisfy
--   $$\theta^*(x;d)=\theta'(x;d)\qquad\text{for every }d.$$
--   The joint limit permits the direction to vary while the step length tends to zero. This is used for the tangent-cone necessary condition.
--
--   **Formalization Note** The statement uses a finite-dimensional real normed space and a real-valued function.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 4, §2.3

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem hadamard_of_lipschitz {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (x : V) (θ' : V → ℝ)
    (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : LipschitzOnWith L θ U)
    (hDiff : ∀ d, HasDirDerivAt θ x d (θ' d)) :
    ∀ d, HasHadamardDirDerivAt θ x d (θ' d) := by sorry
end BilevelSOC.SecondOrder
