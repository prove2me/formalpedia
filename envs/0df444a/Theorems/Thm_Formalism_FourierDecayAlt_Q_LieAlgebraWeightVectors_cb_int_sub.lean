-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_int_sub
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_int_sub
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:44:20.376556+00:00
-- url     : https://prove2.me/theorems/fa9ee733-2484-48d9-8c7a-6d6a08da4f82
-- title:
--   Lie Algebra Weight Vectors: cb int sub
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb int sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L151-L155
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L151-L155

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_InLieW
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_CbStrictMonoOfAnti
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.Q Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_int_sub {x y c : ℝ} (hx : ∃ n : ℤ, x - c = n) (hy : ∃ n : ℤ, y - c = n) :
    ∃ n : ℤ, x - y = n := by sorry
