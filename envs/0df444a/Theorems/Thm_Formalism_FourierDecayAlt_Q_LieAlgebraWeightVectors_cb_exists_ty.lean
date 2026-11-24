-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_exists_ty
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_exists_ty
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T16:45:22.522457+00:00
-- url     : https://prove2.me/theorems/5bfae4cc-3db5-490c-a8c8-d00393eb5d0d
-- title:
--   Lie Algebra Weight Vectors: cb exists ty
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb exists ty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L115-L134
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L115-L134

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_exists_ty (Q : M.Par) (v : ℕ → ℝ)
    (hv : ∀ j : Fin (Q.k - 1), Q.lo (j.1 + 1) ≤ v (j.1 + 1) ∧ v (j.1 + 1) ≤ Q.hi (j.1 + 1) ∧
      ∃ n : ℤ, v (j.1 + 1) - Q.lo (j.1 + 1) = n) :
    ∃ τ : M.Ty Q, ∀ j : Fin (Q.k - 1), M.rho Q τ (j.1 + 1) = v (j.1 + 1) := by sorry
