-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lowK_inv
-- name    : Formalism.FourierDecayAlt.P.Ux2.lowK_inv
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T15:23:03.270087+00:00
-- url     : https://prove2.me/theorems/f166f32c-a5ef-40bf-a0a0-798e34f5d932
-- title:
--   Ux2: low K inv
-- statement:
--   The Ux2 construction uses the low K inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L398-L412
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L398-L412

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulDiagOfTriangular
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixTranspose
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U Formalism.REAL Formalism.QuantumDeterminants
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux2
variable {p : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux2.lowK_inv {L : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kL p) L) :
    uniK (kL p) L⁻¹ ∧ L * L⁻¹ = 1 ∧ L⁻¹ * L = 1 := by sorry
