-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_lo_int
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_lo_int
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:44:45.608026+00:00
-- url     : https://prove2.me/theorems/390bb0de-a6b8-460a-8d03-ea1be1ee2eae
-- title:
--   Lie Algebra Weight Vectors: cb lo int
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb lo int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L136-L143
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L136-L143

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_lo_int (Q : M.Par) (c : ℝ) (i : ℕ) (hu : ∃ n : ℤ, Q.u (i + 1) - c = n)
    (hu' : ∃ n : ℤ, Q.u' (i + 1) - c = n) : ∃ n : ℤ, Q.lo i - (c + 1 / 2) = n := by sorry
