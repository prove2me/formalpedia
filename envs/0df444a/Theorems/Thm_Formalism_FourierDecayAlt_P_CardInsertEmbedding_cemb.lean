-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_cemb
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.cemb
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:13:36.283804+00:00
-- url     : https://prove2.me/theorems/6f14f150-8805-475a-b1e5-775eb1dab0df
-- title:
--   Card Insert Embedding: cemb
-- statement:
--   The Card Insert Embedding construction uses the cemb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L25-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L25-L44

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

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.cemb {m n k : ℕ} (b : Fin m) (hb : n < b.val) (h : (insert b (C2.iSet m n)).card = k) (t : Fin k) :
    (insert b (C2.iSet m n)).orderEmbOfFin h t = if ht : t.val < n then ⟨t.val, by omega⟩ else b := by sorry
