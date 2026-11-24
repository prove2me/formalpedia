-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_ldeg_pullE
-- name    : Formalism.MainNotions.PlaneGram.TwistData.ldeg_pullE
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:05:58.041941+00:00
-- url     : https://prove2.me/theorems/e0f3b9fc-b7d7-4985-8160-0616544ebd91
-- title:
--   Twist Data: ldeg pull E
-- statement:
--   The Twist Data construction uses the ldeg pull E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/MonomialMemPolKSg.lean#L33-L36

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_MonomialMemPolKSg
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
variable {K : Type} [Field K] (D : TwistData K) (j : Fin D.J)

theorem Formalism.MainNotions.PlaneGram.TwistData.ldeg_pullE (ζ : D.EM) (k : Fin (D.nB j + D.r)) :
    ldeg (D.pullE j ζ) k = ldeg ζ (D.e0 j k) := by sorry
