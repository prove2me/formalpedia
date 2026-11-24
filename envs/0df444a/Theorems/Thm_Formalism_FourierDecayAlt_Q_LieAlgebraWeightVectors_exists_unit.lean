-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_exists_unit
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_unit
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:05:29.516314+00:00
-- url     : https://prove2.me/theorems/2f5120c2-2216-4c37-a857-a73a5544cbf0
-- title:
--   Lie Algebra Weight Vectors: exists unit
-- statement:
--   The Lie Algebra Weight Vectors construction uses the exists unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L288-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L288-L310

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_GANormSqStar
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_QuadraticFormTwoTwo_ExistsFrameOfPositiveVector
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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_unit {z a : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (ha : inWb k r a)
    (hind : ∀ c : ℂ, a ≠ c • z) :
    ∃ e : Fin (2 * r + k + 1) → ℂ, inWb k r e ∧ herm (Hpk k r) e z = 0 ∧ herm (Hpk k r) e e = 1 ∧
      ∀ v, herm (Hpk k r) v a = 0 → herm (Hpk k r) v z = 0 → herm (Hpk k r) v e = 0 := by sorry
