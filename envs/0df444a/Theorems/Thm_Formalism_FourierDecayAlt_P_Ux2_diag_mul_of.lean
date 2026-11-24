-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_diag_mul_of
-- name    : Formalism.FourierDecayAlt.P.Ux2.diag_mul_of
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:59:18.132863+00:00
-- url     : https://prove2.me/theorems/a45ef798-c31f-4b50-8ad6-28611baf659f
-- title:
--   Ux2: diag mul of
-- statement:
--   The Ux2 construction uses the diag mul of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L366-L369
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L366-L369

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

theorem Formalism.FourierDecayAlt.P.Ux2.diag_mul_of {κ : Fin p → ℤ} (hκ : Function.Injective κ) {M N : Matrix (Fin p) (Fin p) ℂ}
    (hM : ∀ a b, κ a < κ b → M a b = 0) (hN : ∀ a b, κ a < κ b → N a b = 0) (i : Fin p) :
    (M * N) i i = M i i * N i i := by sorry
