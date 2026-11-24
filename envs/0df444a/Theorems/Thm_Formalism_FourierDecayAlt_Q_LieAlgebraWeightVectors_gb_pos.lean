-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_gb_pos
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_pos
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:02:03.990542+00:00
-- url     : https://prove2.me/theorems/a5ea1ed5-90cd-492f-90e4-7a67783d9a78
-- title:
--   Lie Algebra Weight Vectors: gb pos
-- statement:
--   The Lie Algebra Weight Vectors construction uses the gb pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L94-L159
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L94-L159

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.gb_pos {z v : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hT : 0 < Tz k r z) (hv : inWb k r v)
    (hvz : herm (Hpk k r) v z = 0) (hv0 : v ≠ 0) : 0 < (herm (Hpk k r) v v).re := by sorry
