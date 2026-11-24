-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantReindex_det_reindex
-- name    : Formalism.FourierDecayAlt.P.DeterminantReindex.det_reindex
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:20.855802+00:00
-- url     : https://prove2.me/theorems/8e6ce899-7e65-4f77-b9df-1525e833aa92
-- title:
--   Determinant Reindex: det reindex
-- statement:
--   The Determinant Reindex construction uses the det reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L19-L24

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

theorem Formalism.FourierDecayAlt.P.DeterminantReindex.det_reindex {m k : ℕ} (M : Matrix (Fin m) (Fin m) ℂ) (e ρ f : Fin k → Fin m) (τ : Equiv.Perm (Fin k))
    (h : ∀ t, e t = ρ (τ t)) :
    (M.submatrix e f).det = ((Equiv.Perm.sign τ : ℤ) : ℂ) * (M.submatrix ρ f).det := by sorry
