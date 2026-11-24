-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upK_inv
-- name    : Formalism.FourierDecayAlt.P.Ux2.upK_inv
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:22:36.160191+00:00
-- url     : https://prove2.me/theorems/be3520f3-9820-4b59-8d1b-bbf496fd1213
-- title:
--   Ux2: up K inv
-- statement:
--   The Ux2 construction uses the up K inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L414-L426
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L414-L426

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

theorem Formalism.FourierDecayAlt.P.Ux2.upK_inv {U : Matrix (Fin p) (Fin p) ℂ} (h : uniK (kU p) U) :
    uniK (kU p) U⁻¹ ∧ U * U⁻¹ = 1 ∧ U⁻¹ * U = 1 := by sorry
