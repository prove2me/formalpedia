-- Prove2me | Theorems.Thm_ClassicalComplexWPT_classicalComplexWeierstrassPreparation
-- name    : ClassicalComplexWPT.classicalComplexWeierstrassPreparation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:14:49.780735+00:00
-- url     : https://prove2.me/theorems/c4c67524-7fd1-5b85-a2b2-8559406eabed
-- title:
--   Classical Complex WPT: classical Complex Weierstrass Preparation
-- statement:
--   Classical complex-analytic Weierstrass preparation at the origin, including
--   existence and uniqueness of every coefficient germ and of the unit germ. The
--   statement includes `n = 0` and `d = 0`.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Main.lean#L21-L32
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/Main.lean#L21-L32

import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
import Definitions.Def_ClassicalComplexWPT_PublicExistence
import Definitions.Def_ClassicalComplexWPT_Main
set_option autoImplicit true
open Filter
open scoped BigOperators Topology
open ClassicalComplexWPT

theorem ClassicalComplexWPT.classicalComplexWeierstrassPreparation
    (n d : ℕ) (f : Ambient n → ℂ)
    (hf : AnalyticAt ℂ f 0)
    (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f d a u ∧
      ∀ (a' : Fin d → Base n → ℂ) (u' : Ambient n → ℂ),
        IsWeierstrassPreparation f d a' u' →
        (∀ i, a i =ᶠ[𝓝 0] a' i) ∧ u =ᶠ[𝓝 0] u' := by sorry
