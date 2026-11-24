-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DeterminantReindex_U_mul_sub
-- name    : Formalism.FourierDecayAlt.P.DeterminantReindex.U_mul_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T16:12:47.984995+00:00
-- url     : https://prove2.me/theorems/2e77b32d-0670-4061-a91a-290ed19545a9
-- title:
--   Determinant Reindex: U mul sub
-- statement:
--   The Determinant Reindex construction uses the U mul sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DeterminantReindex.lean#L34-L41

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

theorem Formalism.FourierDecayAlt.P.DeterminantReindex.U_mul_sub {m k : ℕ} (hkm : k ≤ m) (M U : Matrix (Fin m) (Fin m) ℂ) (hU : ∀ i j, j < i → U i j = 0)
    (e f : Fin k → Fin m) (hf : ∀ t, (f t).val = t.val) :
    (M * U).submatrix e f = M.submatrix e f * U.submatrix f f := by sorry
