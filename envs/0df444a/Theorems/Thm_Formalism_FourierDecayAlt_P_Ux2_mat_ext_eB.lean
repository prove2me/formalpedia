-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_mat_ext_eB
-- name    : Formalism.FourierDecayAlt.P.Ux2.mat_ext_eB
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T14:47:51.626813+00:00
-- url     : https://prove2.me/theorems/00d911c6-fc96-45a5-a665-56aa457b54d7
-- title:
--   Ux2: mat ext e B
-- statement:
--   The Ux2 construction uses the mat ext e B property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L26-L29

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

theorem Formalism.FourierDecayAlt.P.Ux2.mat_ext_eB {M N : B.Mat k (j + ρ)}
    (h : ∀ x y, M (eB k j ρ x) (eB k j ρ y) = N (eB k j ρ x) (eB k j ρ y)) : M = N := by sorry
