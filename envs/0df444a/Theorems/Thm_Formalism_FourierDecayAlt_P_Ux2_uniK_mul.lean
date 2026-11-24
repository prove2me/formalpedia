-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_uniK_mul
-- name    : Formalism.FourierDecayAlt.P.Ux2.uniK_mul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:53:38.492836+00:00
-- url     : https://prove2.me/theorems/e493dba5-5220-4e60-a797-af06a6c4b4e7
-- title:
--   Ux2: uni K mul
-- statement:
--   The Ux2 construction uses the uni K mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L371-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L371-L378

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

theorem Formalism.FourierDecayAlt.P.Ux2.uniK_mul {κ : Fin p → ℤ} (hκ : Function.Injective κ) {M N : Matrix (Fin p) (Fin p) ℂ}
    (hM : uniK κ M) (hN : uniK κ N) : uniK κ (M * N) := by sorry
