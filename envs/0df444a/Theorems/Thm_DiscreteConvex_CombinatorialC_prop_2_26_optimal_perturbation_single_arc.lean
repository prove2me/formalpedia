-- Prove2me | Theorems.Thm_DiscreteConvex_CombinatorialC_prop_2_26_optimal_perturbation_single_arc
-- name    : DiscreteConvex.CombinatorialC.prop_2_26_optimal_perturbation_single_arc
-- status  : Disproved
-- author  : @Shuze Chen
-- created : 2026-09-27T21:47:02.304833+00:00
-- url     : https://prove2.me/theorems/b8a69871-660b-4c7c-94cd-b7f517909bf1
-- title:
--   Proposition 2.26 -- optimality survives a small single-arc weight perturbation
-- statement:
--   There is $\alpha_0>0$ such that $\xi_1$ stays optimal for $w_1-\alpha\chi_a$ and $\xi_2$ for $w_2+\alpha\chi_a$, $\alpha\in[0,\alpha_0]$.
--
--   (Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.87, Proposition 2.26.)
-- source:
--   Murota, Discrete Convex Analysis, SIAM 2003, DOI 10.1137/1.9780898718508, p.87, Proposition 2.26

import Mathlib
import Definitions.Def_DiscreteConvex_CombinatorialC_IsOptimalCirc
import Definitions.Def_DiscreteConvex_CombinatorialC_CharVec

/-!
Murota, *Discrete Convex Analysis*, SIAM 2003, p.87, Proposition 2.26, in
`DiscreteConvex.CombinatorialC`.
-/

namespace DiscreteConvex.CombinatorialC

/-- **Proposition 2.26.** There exists `α₀ > 0` such that `ξ1` is optimal for `w1 - αχ_a` and
`ξ2` is optimal for `w2 + αχ_a` for all `α ∈ [0, α₀]`. -/
theorem prop_2_26_optimal_perturbation_single_arc {V A : Type*} [Fintype A] [Fintype V]
    [DecidableEq V] [DecidableEq A] (src dst : A → V) (w1 w2 c : A → ℝ) (a : A)
    (xi1 xi2 : A → ℝ) (hxi1 : IsOptimalCirc src dst w1 c xi1)
    (hxi2 : IsOptimalCirc src dst w2 c xi2) :
    ∃ α0 : ℝ, 0 < α0 ∧ ∀ α : ℝ, 0 ≤ α → α ≤ α0 →
      IsOptimalCirc src dst (w1 - α • CharVec a) c xi1 ∧
        IsOptimalCirc src dst (w2 + α • CharVec a) c xi2 := by sorry

end DiscreteConvex.CombinatorialC
