-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_second_embedding_label_index_zero
-- name    : Formalism.MainNotions.PlaneGram.TwistData.second_embedding_label_index_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T10:06:08.709166+00:00
-- url     : https://prove2.me/theorems/2ebbfee8-9d07-4bd7-8b79-6cac920720d1
-- title:
--   Twist Data: second embedding label index zero
-- statement:
--   The Twist Data construction uses the second embedding label index zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L78-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SecondEmbeddingTangentIndex.lean#L78-L89

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

theorem Formalism.MainNotions.PlaneGram.TwistData.second_embedding_label_index_zero (l : Fin (D.nB j + D.r)) (m : Fin D.r) (h : D.e1 j l = D.mlab (j, m)) :
    m.val = 0 := by sorry
