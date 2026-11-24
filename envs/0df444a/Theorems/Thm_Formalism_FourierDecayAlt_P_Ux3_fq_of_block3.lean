-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_fq_of_block3
-- name    : Formalism.FourierDecayAlt.P.Ux3.fq_of_block3
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:20.024344+00:00
-- url     : https://prove2.me/theorems/7db775f8-9fd6-452a-8613-bf0bb6377957
-- title:
--   Ux3: fq of block3
-- statement:
--   The Ux3 construction uses the fq of block3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L329-L342
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L329-L342

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux3.fq_of_block3 (Fj Fj' : Matrix (Fin (2 * ρ + k + 1)) (Fin (ρ + 1)) ℂ)
    (Q11 : Matrix (Fin j) (Fin j) ℂ) (Q12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (ColumnFamilies : Matrix (Fin j) (Fin j) ℂ)
    (Q21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (Q22 : B.Mat k ρ) (Q23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (Q31 : Matrix (Fin j) (Fin j) ℂ) (Q32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (Q33 : Matrix (Fin j) (Fin j) ℂ) :
    (Matrix.reindex (eB k j ρ) (eC j ρ) (F0 Fj))ᴴ * blk3 Q11 Q12 ColumnFamilies Q21 Q22 Q23 Q31 Q32 Q33 *
        Matrix.reindex (eB k j ρ) (eC j ρ) (F0 Fj') =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks Q11 (Q12 * Fj') (Fjᴴ * Q21) (Fjᴴ * Q22 * Fj')) := by sorry
