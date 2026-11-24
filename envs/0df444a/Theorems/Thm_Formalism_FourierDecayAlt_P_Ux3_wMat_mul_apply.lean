-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_apply
-- name    : Formalism.FourierDecayAlt.P.Ux3.wMat_mul_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T14:47:42.229365+00:00
-- url     : https://prove2.me/theorems/0a8705d5-7176-468d-8815-c5e50d235627
-- title:
--   Ux3: w Mat mul apply
-- statement:
--   The Ux3 construction uses the w Mat mul apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L55-L57
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L55-L57

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

theorem Formalism.FourierDecayAlt.P.Ux3.wMat_mul_apply {n : ℕ} {m : Type*} (A : Matrix (Fin n) m ℂ) (a : Fin n) (b : m) :
    (G.wMat n * A) a b = A a.rev b := by sorry
