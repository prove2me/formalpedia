-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_cancel_left
-- name    : Formalism.FourierDecayAlt.P.Ux3.cancel_left
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T15:23:18.23896+00:00
-- url     : https://prove2.me/theorems/f6411096-ded6-413f-ab8e-d5d2cbc404f9
-- title:
--   Ux3: cancel left
-- statement:
--   The Ux3 construction uses the cancel left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L467-L470
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L467-L470

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

theorem Formalism.FourierDecayAlt.P.Ux3.cancel_left {m : Type*} {n : ℕ} (X : Matrix (Fin n) m ℂ) (W : Matrix (Fin n) (Fin n) ℂ) (hW : IsUnit W.det)
    (h : W * X = 0) : X = 0 := by sorry
