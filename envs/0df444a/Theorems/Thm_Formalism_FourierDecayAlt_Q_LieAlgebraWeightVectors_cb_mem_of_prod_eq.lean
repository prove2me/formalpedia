-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_mem_of_prod_eq
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_mem_of_prod_eq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:44:56.512789+00:00
-- url     : https://prove2.me/theorems/dc8ed69e-a346-4fb1-ac20-0df219dc81a1
-- title:
--   Lie Algebra Weight Vectors: cb mem of prod eq
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb mem of prod eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L26-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L26-L36

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_mem_of_prod_eq {n : ℕ} {a b : ℕ → ℝ}
    (h : ∀ Y : ℂ, ∏ i ∈ Icc 1 n, (Y + (a i : ℂ)) = ∏ i ∈ Icc 1 n, (Y + (b i : ℂ))) :
    ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j := by sorry
