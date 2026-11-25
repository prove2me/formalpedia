-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_sq
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_sq
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:37:31.973146+00:00
-- url     : https://prove2.me/theorems/a2bcad36-a629-44bc-8be2-fd83c274fbe0
-- title:
--   Lie Algebra Weight Vectors: gb sq
-- statement:
--   The Lie Algebra Weight Vectors construction uses the gb sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L82-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L82-L92

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_sq {v : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hl : v (wI k r (Fin.last k)) = 0) :
    (herm (Hpk k r) v v).re = ∑ i, Complex.normSq (v i) := by sorry
