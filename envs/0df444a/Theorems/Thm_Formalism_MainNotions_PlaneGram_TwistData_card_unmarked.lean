-- Prove2me | Theorems.Thm_Formalism_MainNotions_PlaneGram_TwistData_card_unmarked
-- name    : Formalism.MainNotions.PlaneGram.TwistData.card_unmarked
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T10:04:26.594842+00:00
-- url     : https://prove2.me/theorems/9bd04aa7-1458-4aee-b007-981a7bc43ade
-- title:
--   Twist Data: card unmarked
-- statement:
--   The Twist Data construction uses the card unmarked property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L67-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MonomialOrderSegments/SubstitutionXFirstEmbedding.lean#L67-L83

import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SecondEmbeddingTangentIndex
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MonomialOrderSegments_SubstitutionXFirstEmbedding
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

theorem Formalism.MainNotions.PlaneGram.TwistData.card_unmarked (o : Finset (Fin (D.nB j + D.r))) (hM : ¬ D.Marked j o) (m : Fin D.r) :
    (o.filter fun l => l.val < D.stg j m ∧ (D.msg ∘ D.e0 j) l = true).card < D.r := by sorry
