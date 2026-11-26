-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_isWeierstrassPreparation
-- name    : ClassicalComplexWPT.exists_isWeierstrassPreparation
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T18:11:10.700462+00:00
-- url     : https://prove2.me/theorems/1db57879-8cb8-47fd-bce8-4702231da6bc
-- title:
--   Classical Complex WPT: exists is Weierstrass Preparation
-- statement:
--   The existence half of classical complex Weierstrass preparation, in the
--   exact public predicate.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L213-L256
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L213-L256

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.exists_isWeierstrassPreparation {n d : ℕ} {f : Ambient n → ℂ}
    (hf : AnalyticAt ℂ f 0) (horder : ExactOrderInLastVariable f d) :
    ∃ (a : Fin d → Base n → ℂ) (u : Ambient n → ℂ),
      IsWeierstrassPreparation f d a u := by sorry
