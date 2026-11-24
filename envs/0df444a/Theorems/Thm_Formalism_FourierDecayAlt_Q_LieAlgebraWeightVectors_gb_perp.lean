-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_perp
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_perp
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:45:58.536618+00:00
-- url     : https://prove2.me/theorems/af01320d-a4a2-4a86-ba9d-329cb79cf513
-- title:
--   Lie Algebra Weight Vectors: gb perp
-- statement:
--   The Lie Algebra Weight Vectors construction uses the gb perp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L185-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L185-L236

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_perp {m : ℕ} (hm : m + 2 < k + 1) (cs : Fin m → Fin (2 * r + k + 1) → ℂ)
    (a b : Fin (2 * r + k + 1) → ℂ) :
    ∃ v, v ≠ 0 ∧ inWb k r v ∧ herm (Hpk k r) v a = 0 ∧ herm (Hpk k r) v b = 0 ∧
      ∀ j, herm (Hpk k r) v (cs j) = 0 := by sorry
