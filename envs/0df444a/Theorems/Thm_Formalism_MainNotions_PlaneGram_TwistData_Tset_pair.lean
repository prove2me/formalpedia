-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_Tset_pair
-- name    : Formalism.MainNotions.PlaneGram.TwistData.Tset_pair
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:04:38.144571+00:00
-- url     : https://prove2.me/theorems/6e316ab3-5181-40f3-95b8-3fb4347de9c5
-- title:
--   Twist Data: Tset pair
-- statement:
--   The Twist Data construction uses the Tset pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L51-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/CardLinkIdxMulLe.lean#L51-L61

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CgeZeroIffIntegral
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_ProjKeepsLetter
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DigitPartMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_CardLinkIdxMulLe
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

theorem Formalism.MainNotions.PlaneGram.TwistData.Tset_pair (x y : Fin D.J × Fin D.r) :
    D.Tset x.1 x.2 ⊆ D.Tset y.1 y.2 ∨ D.Tset y.1 y.2 ⊆ D.Tset x.1 x.2 ∨
      Disjoint (D.Tset x.1 x.2) (D.Tset y.1 y.2) := by sorry
