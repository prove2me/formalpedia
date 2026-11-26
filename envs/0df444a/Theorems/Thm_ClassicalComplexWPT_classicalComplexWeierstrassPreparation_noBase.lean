-- Prove2me | Theorems.Thm_ClassicalComplexWPT_classicalComplexWeierstrassPreparation_noBase
-- name    : ClassicalComplexWPT.classicalComplexWeierstrassPreparation_noBase
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:15.990623+00:00
-- url     : https://prove2.me/theorems/8415eb46-27d5-52a4-8ffc-46e6533ebecb
-- title:
--   Classical Complex WPT: classical Complex Weierstrass Preparation no Base
-- statement:
--   When there are no base variables, preparation is precisely the univariate
--   exact-order factorization.  This proves the full public existence-and-
--   uniqueness conclusion for every degree `d` when `n = 0`.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/EdgeCases.lean#L43-L116
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/EdgeCases.lean#L43-L116

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_EdgeCases
set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.classicalComplexWeierstrassPreparation_noBase
    {d : ℕ} {f : Ambient 0 → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base 0 → ℂ) (u : Ambient 0 → ℂ),
      IsWeierstrassPreparation f d a u ∧
      ∀ (a' : Fin d → Base 0 → ℂ) (u' : Ambient 0 → ℂ),
        IsWeierstrassPreparation f d a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by sorry
