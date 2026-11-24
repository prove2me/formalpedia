-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ph_lin_sum
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ph_lin_sum
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:06:21.754252+00:00
-- url     : https://prove2.me/theorems/98618ec6-7955-4f76-95bb-4ac73eba5b12
-- title:
--   Twist Data: ph lin sum
-- statement:
--   The Twist Data construction uses the ph lin sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L36-L38

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
import Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Good_monomial

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
variable {K : Type} [Field K]
open Formalism.MainNotions.PlaneGram.TwistData
variable (D : TwistData K)

theorem Formalism.MainNotions.PlaneGram.TwistData.ph_lin_sum (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.ph p Z = ∑ ζ ∈ Z.support, Z.coeff ζ • D.ph p (monomial ζ 1) := by sorry
