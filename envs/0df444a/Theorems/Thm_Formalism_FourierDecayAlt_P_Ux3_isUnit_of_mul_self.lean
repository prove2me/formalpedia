-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_isUnit_of_mul_self
-- name    : Formalism.FourierDecayAlt.P.Ux3.isUnit_of_mul_self
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T14:58:47.793336+00:00
-- url     : https://prove2.me/theorems/1ff5b2aa-86b2-45dc-be1b-5a7f7cff71c5
-- title:
--   Ux3: is Unit of mul self
-- statement:
--   The Ux3 construction uses the is Unit of mul self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L472-L475
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L472-L475

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_FormalDegreeBessel_FinalG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SymmetricScalarBlockMatrixMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U
set_option linter.unusedSimpArgs false
set_option linter.unnecessarySeqFocus false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux3
variable {k j ρ : ℕ}

theorem Formalism.FourierDecayAlt.P.Ux3.isUnit_of_mul_self {n : ℕ} (W : Matrix (Fin n) (Fin n) ℂ) (h : W * W = 1) : IsUnit W.det := by sorry
