-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_eq_of_prod_eq
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_eq_of_prod_eq
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:04:15.909539+00:00
-- url     : https://prove2.me/theorems/dceff3e6-20a2-4a08-9f06-b007a494fe00
-- title:
--   Lie Algebra Weight Vectors: cb eq of prod eq
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb eq of prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L57-L70
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L57-L70

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_eq_of_prod_eq {n : ℕ} {a b : ℕ → ℝ}
    (ha : ∀ i, 1 ≤ i → i + 1 ≤ n → a (i + 1) < a i) (hb : ∀ i, 1 ≤ i → i + 1 ≤ n → b (i + 1) < b i)
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, a i = b i := by sorry
