-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_eB_lr
-- name    : Formalism.FourierDecayAlt.P.Ux2.eB_lr
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:54:16.520793+00:00
-- url     : https://prove2.me/theorems/41672f72-4629-4b9b-9198-40e09bd704b0
-- title:
--   Ux2: e B lr
-- statement:
--   The Ux2 construction uses the e B lr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L15-L15

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

theorem Formalism.FourierDecayAlt.P.Ux2.eB_lr (v : Fin (2 * ρ + k + 1)) : (eB k j ρ (Sum.inl (Sum.inr v))).val = j + v.val := by sorry
