-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantReindex_sign_pm
-- name    : Formalism.FourierDecayAlt.P.DeterminantReindex.sign_pm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:55.211803+00:00
-- url     : https://prove2.me/theorems/a46464a4-c5aa-4c80-8abd-00b5889e331f
-- title:
--   Determinant Reindex: sign pm
-- statement:
--   The Determinant Reindex construction uses the sign pm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L30-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L30-L32

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CardInsertEmbedding
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DeterminantReindex
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
open Formalism.FourierDecayAlt.P.DeterminantReindex
open C2x2 CardInsertEmbedding

theorem Formalism.FourierDecayAlt.P.DeterminantReindex.sign_pm {k : ℕ} (τ : Equiv.Perm (Fin k)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 ∨ ((Equiv.Perm.sign τ : ℤ) : ℂ) = -1 := by sorry
