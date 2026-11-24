-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_block3_mul
-- name    : Formalism.FourierDecayAlt.P.Ux3.block3_mul
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:48:44.976697+00:00
-- url     : https://prove2.me/theorems/f98f76ff-ca1a-4075-bb0a-3d54953060a9
-- title:
--   Ux3: block3 mul
-- statement:
--   The Ux3 construction uses the block3 mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L14-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L14-L29

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

theorem Formalism.FourierDecayAlt.P.Ux3.block3_mul
    (A11 : Matrix (Fin j) (Fin j) ℂ) (A12 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A13 : Matrix (Fin j) (Fin j) ℂ)
    (A21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (A22 : B.Mat k ρ) (A23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (A31 : Matrix (Fin j) (Fin j) ℂ) (A32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (A33 : Matrix (Fin j) (Fin j) ℂ)
    (ToralGalois : Matrix (Fin j) (Fin j) ℂ) (cocyclesToWachVectorsExponent : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B13 : Matrix (Fin j) (Fin j) ℂ)
    (B21 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ) (B22 : B.Mat k ρ) (B23 : Matrix (Fin (2 * ρ + k + 1)) (Fin j) ℂ)
    (B31 : Matrix (Fin j) (Fin j) ℂ) (B32 : Matrix (Fin j) (Fin (2 * ρ + k + 1)) ℂ) (B33 : Matrix (Fin j) (Fin j) ℂ) :
    blk3 (k := k) (j := j) (ρ := ρ) A11 A12 A13 A21 A22 A23 A31 A32 A33 * blk3 ToralGalois cocyclesToWachVectorsExponent B13 B21 B22 B23 B31 B32 B33 =
      blk3 (A11 * ToralGalois + A12 * B21 + A13 * B31) (A11 * cocyclesToWachVectorsExponent + A12 * B22 + A13 * B32) (A11 * B13 + A12 * B23 + A13 * B33)
        (A21 * ToralGalois + A22 * B21 + A23 * B31) (A21 * cocyclesToWachVectorsExponent + A22 * B22 + A23 * B32) (A21 * B13 + A22 * B23 + A23 * B33)
        (A31 * ToralGalois + A32 * B21 + A33 * B31) (A31 * cocyclesToWachVectorsExponent + A32 * B22 + A33 * B32) (A31 * B13 + A32 * B23 + A33 * B33) := by sorry
