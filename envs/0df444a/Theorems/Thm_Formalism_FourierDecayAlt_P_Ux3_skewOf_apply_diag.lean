-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux3_skewOf_apply_diag
-- name    : Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_diag
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:23:00.09044+00:00
-- url     : https://prove2.me/theorems/2ddd812c-750e-49be-a429-fdd7bd40571d
-- title:
--   Ux3: skew Of apply diag
-- statement:
--   The Ux3 construction uses the skew Of apply diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L493-L495
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SymmetricScalarBlockMatrixMul.lean#L493-L495

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

theorem Formalism.FourierDecayAlt.P.Ux3.skewOf_apply_diag {n : ℕ} (q : (G.UT n → ℂ) × (Fin n → ℝ)) (a : Fin n) :
    skewOf q a a = Complex.I * (q.2 a : ℂ) := by sorry
