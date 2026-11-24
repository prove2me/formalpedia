-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CardInsertEmbedding_submatrix_monomialMatrix_mul
-- name    : Formalism.FourierDecayAlt.P.CardInsertEmbedding.submatrix_monomialMatrix_mul
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:12:33.326807+00:00
-- url     : https://prove2.me/theorems/2a0bcca6-ec64-4f20-ab81-75a0957714c4
-- title:
--   Card Insert Embedding: submatrix monomial Matrix mul
-- statement:
--   The Card Insert Embedding construction uses the submatrix monomial Matrix mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L52-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/CardInsertEmbedding.lean#L52-L63

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

theorem Formalism.FourierDecayAlt.P.CardInsertEmbedding.submatrix_monomialMatrix_mul {m k n : ℕ} (hkn : k = n) (hnm : n ≤ m) (w : Equiv.Perm (Fin m)) (d : Fin m → ℂ)
    (M : Matrix (Fin m) (Fin m) ℂ) (eR eI f : Fin k → Fin m) (hI : ∀ t, (eI t).val = t.val)
    (hR : ∀ t, ∃ j0 : Fin m, j0.val < n ∧ w j0 = eR t) :
    (C2.monoP w d * M).submatrix eR f = (C2.monoP w d).submatrix eR eI * M.submatrix eI f := by sorry
