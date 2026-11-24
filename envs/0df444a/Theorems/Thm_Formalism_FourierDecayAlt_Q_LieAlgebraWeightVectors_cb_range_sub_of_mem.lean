-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_range_sub_of_mem
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_range_sub_of_mem
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:44:54.990498+00:00
-- url     : https://prove2.me/theorems/9863a748-13f1-4b2e-bccc-41719661d873
-- title:
--   Lie Algebra Weight Vectors: cb range sub of mem
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb range sub of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L38-L46

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_range_sub_of_mem {n : ℕ} {a b : ℕ → ℝ} (hm : ∀ i ∈ Icc 1 n, ∃ j ∈ Icc 1 n, a i = b j) :
    Set.range (fun j : Fin n => -a (j.1 + 1)) ⊆ Set.range (fun j : Fin n => -b (j.1 + 1)) := by sorry
