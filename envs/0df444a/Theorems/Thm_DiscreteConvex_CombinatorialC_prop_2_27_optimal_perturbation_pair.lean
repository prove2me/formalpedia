-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_prop_2_27_optimal_perturbation_pair
-- name    : DiscreteConvex.CombinatorialC.prop_2_27_optimal_perturbation_pair
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:46:08.976216+00:00
-- url     : https://prove2.me/theorems/f0e0fa05-d64a-40c7-ac20-90d591c8a042
-- title:
--   Proposition 2.27 -- optimality survives a small paired-arc weight perturbation
-- statement:
--   There is $\alpha_0>0$, uniform over $b\in S\setminus\{a\}$, such that $\xi_1$ stays optimal for $w_1-\alpha(\chi_a-\chi_b)$ and $\xi_2$ for $w_2+\alpha(\chi_a-\chi_b)$, $\alpha\in[0,\alpha_0]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.87, Proposition 2.27.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.87, Proposition 2.27

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsOptimalCirc
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.87, Proposition 2.27, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.27.** There exists `α₀ > 0` such that `ξ1` is optimal for
`w1 - α(χ_a - χ_b)` and `ξ2` is optimal for `w2 + α(χ_a - χ_b)` for all `b ∈ S \ {a}` and for
all `α ∈ [0, α₀]`. -/
theorem prop_2_27_optimal_perturbation_pair {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (S : Finset A) (w1 w2 c : A → ℝ) (a : A)
    (xi1 xi2 : A → ℝ) (hxi1 : IsOptimalCirc src dst w1 c xi1)
    (hxi2 : IsOptimalCirc src dst w2 c xi2) :
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ b ∈ S.erase a, ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      IsOptimalCirc src dst (w1 - α • (CharVec a - CharVec b)) c xi1 ∧
        IsOptimalCirc src dst (w2 + α • (CharVec a - CharVec b)) c xi2 := by sorry

end DiscreteConvex.CombinatorialC
