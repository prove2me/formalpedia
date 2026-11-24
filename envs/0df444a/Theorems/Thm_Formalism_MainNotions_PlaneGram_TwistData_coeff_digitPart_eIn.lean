-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_coeff_digitPart_eIn
-- name    : Formalism.MainNotions.PlaneGram.TwistData.coeff_digitPart_eIn
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:04:20.603656+00:00
-- url     : https://prove2.me/theorems/d77b0bc1-faac-47fa-893a-69cd0ee808e2
-- title:
--   Twist Data: coeff digit Part e In
-- statement:
--   The Twist Data construction uses the coeff digit Part e In property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L78-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutedExponentApplyLabel.lean#L78-L96

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

theorem Formalism.MainNotions.PlaneGram.TwistData.coeff_digitPart_eIn (p : ℕ) {ζ : D.EM} (hζ : D.LabLowE p ζ) (G : MvPolynomial (D.OL × Fin D.r) K) :
    (D.digitPart p (D.labF ζ) G).coeff (eIn D.outP ζ) = G.coeff (D.collapseExponent p ζ) := by sorry
