-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_nxt_prv
-- name    : Formalism.MainNotions.PlaneGram.TwistData.nxt_prv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T02:48:41.337956+00:00
-- url     : https://prove2.me/theorems/59337467-6fcb-48ac-b193-ecd96d0f67a7
-- title:
--   Twist Data: nxt prv
-- statement:
--   The Twist Data construction uses the nxt prv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L257-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SumOnLetterApplyInl.lean#L257-L263

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_DdivOnLetterMonomial
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_AddMemSupportOfMemSupportCoefOut
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SlopeOfBinomCombGen
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SumOnLetterApplyInl
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
variable [CharZero K] (D : TwistData K) (v : AddValuation K (WithTop ℚ)) (p : ℕ)
variable {D v p}
variable (D p)
variable {D p}

theorem Formalism.MainNotions.PlaneGram.TwistData.nxt_prv (D : TwistData K) (j : Fin D.J) : D.nxt (D.aux₃ j) = j := by sorry
