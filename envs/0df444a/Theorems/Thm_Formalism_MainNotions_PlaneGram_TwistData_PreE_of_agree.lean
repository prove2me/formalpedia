-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_PreE_of_agree
-- name    : Formalism.MainNotions.PlaneGram.TwistData.PreE.of_agree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:05:21.120811+00:00
-- url     : https://prove2.me/theorems/ebcc1815-1e06-4269-9e78-063ebd95948e
-- title:
--   Pre E: of agree
-- statement:
--   The Pre E construction uses the of agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L133-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/ExistsOfMemSupportLin.lean#L133-L142

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_TestBoundOfRhoAndNormSets
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SegDefs
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ExistsOfMemSupportLin
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

theorem Formalism.MainNotions.PlaneGram.TwistData.PreE.of_agree {j j' : Fin D.J} (h : j' ≠ j) {ζ ζ' : D.EM} (hζ : D.PreE j' ζ)
    (hag : ∀ i, ¬ D.SegL j i → ∀ a, ζ' (i, a) = ζ (i, a)) : D.PreE j' ζ' := by sorry
