-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_wMat_mul_wMat_mul
-- name    : Formalism.FourierDecayAlt.P.Ux3.wMat_mul_wMat_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T16:26:47.597096+00:00
-- url     : https://prove2.me/theorems/76bfe679-0535-42d2-8f9b-0dd175576d69
-- title:
--   Ux3: w Mat mul w Mat mul
-- statement:
--   The Ux3 construction uses the w Mat mul w Mat mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L624-L625
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L624-L625

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

theorem Formalism.FourierDecayAlt.P.Ux3.wMat_mul_wMat_mul {m : Type*} (n : ℕ) (X : Matrix (Fin n) m ℂ) : G.wMat n * (G.wMat n * X) = X := by sorry
