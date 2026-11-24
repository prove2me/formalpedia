-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_cnt_tp_zero
-- name    : Formalism.MainNotions.PlaneGram.TwistData.cnt_tp_zero
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T10:04:00.734797+00:00
-- url     : https://prove2.me/theorems/6f3d8a17-b54e-4bdc-9be1-e7a467a4ba93
-- title:
--   Twist Data: cnt tp zero
-- statement:
--   The Twist Data construction uses the cnt tp zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L115-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L115-L122

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingInjective
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
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

theorem Formalism.MainNotions.PlaneGram.TwistData.cnt_tp_zero (o : Finset (Fin (D.nB j + D.r))) (m : Fin D.r) (h0 : m.val = 0) :
    D.cnt j o (D.mtp (j, m)) = 0 := by sorry
