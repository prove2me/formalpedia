-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_mul_wP_apply
-- name    : Formalism.FourierDecayAlt.P.Ux2.mul_wP_apply
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:52:59.347017+00:00
-- url     : https://prove2.me/theorems/511ad448-b6c6-432a-95d7-74147e251f88
-- title:
--   Ux2: mul w P apply
-- statement:
--   The Ux2 construction uses the mul w P apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L432-L434
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L432-L434

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

theorem Formalism.FourierDecayAlt.P.Ux2.mul_wP_apply (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (M * wP σ) a b = M a (σ.symm b) := by sorry
