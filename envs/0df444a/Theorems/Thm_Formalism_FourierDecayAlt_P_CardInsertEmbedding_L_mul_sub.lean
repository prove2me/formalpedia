-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_L_mul_sub
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.L_mul_sub
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T16:13:05.647805+00:00
-- url     : https://prove2.me/theorems/30dfd45a-a487-49e4-a3f3-b80f1e4d7d1f
-- title:
--   Card Insert Embedding: L mul sub
-- statement:
--   The Card Insert Embedding construction uses the L mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L65-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L65-L72

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

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.L_mul_sub {m k : ℕ} (hkm : k ≤ m) (L U : Matrix (Fin m) (Fin m) ℂ) (hL : ∀ i j, i < j → L i j = 0)
    (eI f : Fin k → Fin m) (hI : ∀ t, (eI t).val = t.val) :
    (L * U).submatrix eI f = L.submatrix eI eI * U.submatrix eI f := by sorry
