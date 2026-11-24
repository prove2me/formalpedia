-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_card_ins
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.card_ins
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:34:35.242715+00:00
-- url     : https://prove2.me/theorems/9344ad23-a0b9-48e4-98e9-5212f2d05e06
-- title:
--   Card Insert Embedding: card ins
-- statement:
--   The Card Insert Embedding construction uses the card ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L20-L23

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StabilizerAntidiagonalExact
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.P.CardInsertEmbedding
open C2x2

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.card_ins {m n : ℕ} (b : Fin m) (hb : n < b.val) (hn : n ≤ m) :
    (insert b (C2.iSet m n)).card = n + 1 := by sorry
