-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_ffa_fvec_last
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_fvec_last
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T16:04:08.21059+00:00
-- url     : https://prove2.me/theorems/8b7b50bb-48ad-4e39-b8f7-2895e9b71321
-- title:
--   Lie Algebra Weight Vectors: ffa fvec last
-- statement:
--   The Lie Algebra Weight Vectors construction uses the ffa fvec last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L84-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/TopLevelPointwiseIdentity.lean#L84-L86

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_TopLevelPointwiseIdentity
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
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.ffa_fvec_last (z : Fin (2 * r + k + 1) → ℂ) : fvec k r z (Fin.last r) = z := by sorry
