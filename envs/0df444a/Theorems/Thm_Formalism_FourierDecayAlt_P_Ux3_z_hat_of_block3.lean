-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_z_hat_of_block3
-- name    : Formalism.FourierDecayAlt.P.Ux3.z_hat_of_block3
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T15:22:51.746159+00:00
-- url     : https://prove2.me/theorems/157338cd-4f70-47de-9fe1-e56d6b851c3c
-- title:
--   Ux3: z hat of block3
-- statement:
--   The Ux3 construction uses the z hat of block3 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L344-L356
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L344-L356

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

theorem Formalism.FourierDecayAlt.P.Ux3.z_hat_of_block3 (z z' : Fin (2 * (j + ρ) + k + 1) → ℂ) (hz : inWb k (j + ρ) z) (hz' : inWb k (j + ρ) z')
    (product_first_partition : Matrix (Fin j) (Fin j) ℂ) (sizeConstantAtParamsWeight : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (flipOneThree : Matrix (Fin j) (Fin j) ℂ)
    (placeRankTwoOne : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (TaylorLogMetric : B.Mat k ρ) (flipTwoThree : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (BlochKatoReduction : Matrix (Fin j) (Fin j) ℂ) (SumRepresentations : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (ArithmeticCylinders : Matrix (Fin j) (Fin j) ℂ) :
    Zhat k (j + ρ) z z' (blk3 product_first_partition sizeConstantAtParamsWeight flipOneThree placeRankTwoOne TaylorLogMetric flipTwoThree BlochKatoReduction SumRepresentations ArithmeticCylinders) =
      Matrix.reindex (eC j ρ) (eC j ρ) (Matrix.fromBlocks (G.wMat j * BlochKatoReduction)
        (G.wMat j * SumRepresentations * Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z'))
        ((Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))ᴴ * (Hpk k ρ * placeRankTwoOne))
        ((Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z))ᴴ * (Hpk k ρ * TaylorLogMetric) * Formalism.QuantumDeterminants.Fm k ρ (lowV k j ρ z'))) := by sorry
