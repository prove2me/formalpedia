-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_vge_coeff_GM
-- name    : Formalism.MainNotions.PlaneGram.TwistData.vge_coeff_GM
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:06:15.838918+00:00
-- url     : https://prove2.me/theorems/2190659c-ece7-4d15-a856-8c96991109b1
-- title:
--   Twist Data: vge coeff GM
-- statement:
--   The Twist Data construction uses the vge coeff GM property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L160-L171
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L160-L171

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
variable [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ}

theorem Formalism.MainNotions.PlaneGram.TwistData.vge_coeff_GM (hD : DVRHyp v p) (hV : D.Valid v p) {F : MvPolynomial (D.OL × Fin D.r) K}
    (hF : F ∈ PolK K D.r D.dO) (hF0 : bge v 0 F) (ζ : D.EM) :
    vge v (-D.n0 v) ((D.GM F (D.tpE ζ)).coeff (D.collapseExponent p ζ)) := by sorry
