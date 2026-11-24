-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_wMat_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Ux2.wMat_mul_apply
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:48:52.598604+00:00
-- url     : https://prove2.me/theorems/93285a2e-86bc-4cfb-bc4d-80948bca378a
-- title:
--   Ux2: w Mat mul apply
-- statement:
--   The Ux2 construction uses the w Mat mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L66-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L66-L68

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
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux2.wMat_mul_apply {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (i j : Fin d) :
    (G.wMat d * M) i j = M i.rev j := by sorry
