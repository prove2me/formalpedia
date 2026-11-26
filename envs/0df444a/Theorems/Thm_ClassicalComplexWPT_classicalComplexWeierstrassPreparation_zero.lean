-- Prove2me | Theorems.Thm_ClassicalComplexWPT_classicalComplexWeierstrassPreparation_zero
-- name    : ClassicalComplexWPT.classicalComplexWeierstrassPreparation_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:57:13.991484+00:00
-- url     : https://prove2.me/theorems/83e30f2d-b07c-5c78-80f9-7eaa9b10bce3
-- title:
--   Classical Complex WPT: classical Complex Weierstrass Preparation zero
-- statement:
--   Degree-zero preparation, including uniqueness of the empty coefficient family and the unit.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/EdgeCases.lean#L21-L36
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/EdgeCases.lean#L21-L36

import Definitions.Def_ClassicalComplexWPT_ExactOrder
import Definitions.Def_ClassicalComplexWPT_EdgeCases
set_option autoImplicit true
open Filter
open scoped Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.classicalComplexWeierstrassPreparation_zero
    {n : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f 0) :
    ∃ (a : Fin 0 → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f 0 a u ∧
      ∀ (a' : Fin 0 → Base n → ℂ) (u' : Ambient n → ℂ),
        IsWeierstrassPreparation f 0 a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by sorry
