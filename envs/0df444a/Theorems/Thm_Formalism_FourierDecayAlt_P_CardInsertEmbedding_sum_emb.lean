-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_sum_emb
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.sum_emb
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T15:33:49.348801+00:00
-- url     : https://prove2.me/theorems/3d6cac5c-9c8c-4c60-b603-12c74166f3c8
-- title:
--   Card Insert Embedding: sum emb
-- statement:
--   The Card Insert Embedding construction uses the sum emb property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L46-L50
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L46-L50

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

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.sum_emb {m k : ℕ} (hkm : k ≤ m) (e : Fin k → Fin m) (he : ∀ t, (e t).val = t.val) (g : Fin m → ℂ)
    (hg : ∀ j : Fin m, k ≤ j.val → g j = 0) : ∑ j, g j = ∑ t, g (e t) := by sorry
