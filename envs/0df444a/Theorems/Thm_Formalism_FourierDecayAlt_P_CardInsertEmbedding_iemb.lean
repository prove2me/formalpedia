-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_iemb
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.iemb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:34:23.693097+00:00
-- url     : https://prove2.me/theorems/9ba1c604-0fbd-4106-b659-eeafcbf1b353
-- title:
--   Card Insert Embedding: iemb
-- statement:
--   The Card Insert Embedding construction uses the iemb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L11-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L11-L18

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

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.iemb {m n k : ℕ} (hn : n ≤ m) (h : (C2.iSet m n).card = k) (t : Fin k) :
    ((C2.iSet m n).orderEmbOfFin h t).val = t.val := by sorry
