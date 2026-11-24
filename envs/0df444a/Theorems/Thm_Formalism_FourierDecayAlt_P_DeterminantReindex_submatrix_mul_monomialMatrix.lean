-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantReindex_submatrix_mul_monomialMatrix
-- name    : Formalism.FourierDecayAlt.P.DeterminantReindex.submatrix_mul_monomialMatrix
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:56.861187+00:00
-- url     : https://prove2.me/theorems/65529b1d-9243-445f-82a3-ff449331d6af
-- title:
--   Determinant Reindex: submatrix mul monomial Matrix
-- statement:
--   The Determinant Reindex construction uses the submatrix mul monomial Matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L43-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L43-L49

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

theorem Formalism.FourierDecayAlt.P.DeterminantReindex.submatrix_mul_monomialMatrix {m k : ℕ} (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ) (M : Matrix (Fin m) (Fin m) ℂ)
    (e f : Fin k → Fin m) :
    (M * C2.monoP w d).submatrix e f = M.submatrix e (fun s => w (f s)) * Matrix.diagonal (fun s => d (f s)) := by sorry
