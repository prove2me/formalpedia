-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_symm
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_symm
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T16:04:42.412335+00:00
-- url     : https://prove2.me/theorems/ab368d15-7e34-4bf4-9332-c8a9c9111377
-- title:
--   Lie Algebra Weight Vectors: gb symm
-- statement:
--   The Lie Algebra Weight Vectors construction uses the gb symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L48-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L48-L52

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_symm {v w : Fin (2 * r + k + 1) → ℂ} (hv : inWb k r v) (hw : inWb k r w) :
    herm (Hpk k r) v w = star (herm (Hpk k r) w v) := by sorry
