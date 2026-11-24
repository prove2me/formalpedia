-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_permutationMatrix_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Ux2.permutationMatrix_mul_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T14:49:44.580951+00:00
-- url     : https://prove2.me/theorems/9dfdc5e2-2da0-4fb9-b290-2265771212d7
-- title:
--   Ux2: permutation Matrix mul apply
-- statement:
--   The Ux2 construction uses the permutation Matrix mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L428-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L428-L430

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

theorem Formalism.FourierDecayAlt.P.Ux2.permutationMatrix_mul_apply (σ : Equiv.Perm (Fin p)) (M : Matrix (Fin p) (Fin p) ℂ) (a b : Fin p) :
    (wP σ * M) a b = M (σ a) b := by sorry
