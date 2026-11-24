-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux2_upper_eq
-- name    : Formalism.FourierDecayAlt.P.Ux2.upper_eq
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T15:22:42.293603+00:00
-- url     : https://prove2.me/theorems/db4fc1d4-968d-4797-81b7-5128dd0b1751
-- title:
--   Ux2: upper eq
-- statement:
--   The Ux2 construction uses the upper eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L545-L551
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixTranspose.lean#L545-L551

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

theorem Formalism.FourierDecayAlt.P.Ux2.upper_eq {u : Matrix (Fin p) (Fin p) ℂ} (hu : uniK (kU p) u) : u = G.upper (fun q => u q.1.1 q.1.2) := by sorry
