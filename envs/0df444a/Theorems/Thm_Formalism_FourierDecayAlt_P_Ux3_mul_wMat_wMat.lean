-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_mul_wMat_wMat
-- name    : Formalism.FourierDecayAlt.P.Ux3.mul_wMat_wMat
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:26:10.704952+00:00
-- url     : https://prove2.me/theorems/38cba1bb-4e07-4e53-8b73-25740de2628a
-- title:
--   Ux3: mul w Mat w Mat
-- statement:
--   The Ux3 construction uses the mul w Mat w Mat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L233-L234
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L233-L234

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

theorem Formalism.FourierDecayAlt.P.Ux3.mul_wMat_wMat {m : Type*} (n : ℕ) (M : Matrix m (Fin n) ℂ) : M * G.wMat n * G.wMat n = M := by sorry
