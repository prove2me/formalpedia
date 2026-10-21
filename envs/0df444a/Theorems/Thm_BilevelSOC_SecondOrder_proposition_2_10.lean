-- Prove2me | Theorems.Thm_BilevelSOC_SecondOrder_proposition_2_10
-- name    : BilevelSOC.SecondOrder.proposition_2_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:00.858366+00:00
-- url     : https://prove2.me/theorems/39c087e4-665a-4286-aa38-1f2b86e9792f
-- title:
--   Proposition 2.10 — directional second-order growth criterion
-- statement:
--   Let $\theta$ be second-order directionally differentiable and second-order epi-regular at $x$. Suppose $\theta'(x;d)\ge0$ for every direction, and the second-order derivative has a positive infimum over $w$ for each nonzero direction with $\theta'(x;d)=0$. Then $\theta$ has second-order growth at $x$:
--   $$\exists C>0,\ \exists U\ni x,\ \forall z\in U:\quad \theta(z)\ge\theta(x)+C\|z-x\|^2.$$
--   This is the unconstrained growth criterion used on the auxiliary maximum.
--
--   **Formalization Note** A local Lipschitz hypothesis is added relative to the printed proposition, as disclosed in the mission notes. The positive infimum is stated by a uniform positive lower bound, avoiding a default real infimum.
-- source:
--   Mehlitz & Zemkoho, Sufficient Optimality Conditions in Bilevel Programming, arXiv:1911.01647v1, p. 8, Proposition 2.10

import Definitions.Def_BilevelSOC_SecondOrder_Model
open scoped Topology

namespace BilevelSOC.SecondOrder
theorem proposition_2_10 {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] (θ : V → ℝ) (x : V)
    (θ' : V → ℝ) (θ'' : V → V → ℝ)
    (hDiff : SecondOrderDirDiff θ x θ' θ'')
    (hEpi : SecondOrderEpiRegular θ x θ' θ'')
    (U : Set V) (hU : U ∈ 𝓝 x) (L : NNReal)
    (hLip : LipschitzOnWith L θ U)
    (hFirst : ∀ d, 0 ≤ θ' d)
    (hSecond : ∀ d, θ' d = 0 → d ≠ 0 → ∃ c : ℝ, 0 < c ∧ ∀ w, c ≤ θ'' d w) :
    GrowthCondition θ Set.univ x 2 := by sorry
end BilevelSOC.SecondOrder
