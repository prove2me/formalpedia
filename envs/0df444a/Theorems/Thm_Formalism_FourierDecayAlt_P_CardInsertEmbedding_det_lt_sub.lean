-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_det_lt_sub
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.det_lt_sub
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:30:31.744803+00:00
-- url     : https://prove2.me/theorems/88b2f0a3-b2bd-47fb-ab68-d28b8a52c3e4
-- title:
--   Card Insert Embedding: det lt sub
-- statement:
--   The Card Insert Embedding construction uses the det lt sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L74-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L74-L82

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

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.det_lt_sub {m k : ℕ} (l : Matrix (Fin m) (Fin m) ℂ) (hl : l ∈ C2.LTset m) (eI : Fin k → Fin m)
    (hI : ∀ t, (eI t).val = t.val) : (l.submatrix eI eI).det = 1 := by sorry
