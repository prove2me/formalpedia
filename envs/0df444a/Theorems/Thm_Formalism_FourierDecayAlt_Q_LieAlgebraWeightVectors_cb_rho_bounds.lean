-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_cb_rho_bounds
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_rho_bounds
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T15:46:37.287417+00:00
-- url     : https://prove2.me/theorems/24e65e68-256c-4846-b9c0-68423d0c2e13
-- title:
--   Lie Algebra Weight Vectors: cb rho bounds
-- statement:
--   The Lie Algebra Weight Vectors construction uses the cb rho bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L83-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/CbStrictMonoOfAnti.lean#L83-L93

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.cb_rho_bounds (Q : M.Par) (hg : ∀ i ∈ Icc 1 (Q.k - 1), Q.lo i ≤ Q.hi i) (π : M.Ty Q)
    (j : Fin (Q.k - 1)) : Q.lo (j.1 + 1) ≤ M.rho Q π (j.1 + 1) ∧ M.rho Q π (j.1 + 1) ≤ Q.hi (j.1 + 1) := by sorry
