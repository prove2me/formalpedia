-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_mul_eB
-- name    : Formalism.FourierDecayAlt.P.Ux2.mul_eB
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:25:41.667712+00:00
-- url     : https://prove2.me/theorems/c1ebcba8-0bbf-4e1d-adc3-f976a8c53c05
-- title:
--   Ux2: mul e B
-- statement:
--   The Ux2 construction uses the mul e B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L31-L35

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

theorem Formalism.FourierDecayAlt.P.Ux2.mul_eB (M N : B.Mat k (j + ρ)) (x y : Ix k j ρ) :
    (M * N) (eB k j ρ x) (eB k j ρ y) =
      ∑ z : Ix k j ρ, M (eB k j ρ x) (eB k j ρ z) * N (eB k j ρ z) (eB k j ρ y) := by sorry
