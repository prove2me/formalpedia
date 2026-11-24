-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_lu_unique
-- name    : Formalism.FourierDecayAlt.P.Ux2.lu_unique
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:25:36.188917+00:00
-- url     : https://prove2.me/theorems/d4fe24ab-bcf7-4753-92bf-e9d2c880d580
-- title:
--   Ux2: lu unique
-- statement:
--   The Ux2 construction uses the lu unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L574-L614
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L574-L614

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

theorem Formalism.FourierDecayAlt.P.Ux2.lu_unique {L1 L2 U1 U2 : Matrix (Fin p) (Fin p) ℂ} (d : Fin p → ℂ) (hd : ∀ i, d i ≠ 0)
    (hL1 : uniK (kL p) L1) (hL2 : uniK (kL p) L2) (hU1 : uniK (kU p) U1) (hU2 : uniK (kU p) U2)
    (h : L1 * diagonal d * U1 = L2 * diagonal d * U2) : L1 = L2 ∧ U1 = U2 := by sorry
