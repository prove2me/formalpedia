-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_prod_choose_add
-- name    : Formalism.MainNotions.PlaneGram.TwistData.prod_choose_add
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:05:34.219563+00:00
-- url     : https://prove2.me/theorems/b3896b33-0a13-4787-aef5-406890b0354b
-- title:
--   Twist Data: prod choose add
-- statement:
--   The Twist Data construction uses the prod choose add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L98-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L98-L103

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_GlobalTheory
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutedExponentApplyLabel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MvPolynomial Finset
open Formalism Formalism.MainNotions Formalism.MainNotions.PlaneGram
open Formalism.MainNotions.PlaneGram.TwistData
variable {K : Type} [Field K] (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.prod_choose_add {σ : Type} [Fintype σ] (β M : σ →₀ ℕ) :
    ((β + M).prod fun x k => (k.choose (M x) : K)) = ((∏ x, (β x + M x).choose (M x) : ℕ) : K) := by sorry
