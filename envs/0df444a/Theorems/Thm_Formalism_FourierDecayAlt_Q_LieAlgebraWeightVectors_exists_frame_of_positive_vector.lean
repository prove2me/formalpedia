-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_Q_LieAlgebraWeightVectors_exists_frame_of_positive_vector
-- name    : Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_frame_of_positive_vector
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T16:44:47.989216+00:00
-- url     : https://prove2.me/theorems/03b026ce-d9b6-47de-912c-b09dea0c78fe
-- title:
--   Lie Algebra Weight Vectors: exists frame of positive vector
-- statement:
--   The Lie Algebra Weight Vectors construction uses the exists frame of positive vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L238-L283
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/QuadraticFormTwoTwo/ExistsFrameOfPositiveVector.lean#L238-L283

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

theorem Formalism.FourierDecayAlt.Q.LieAlgebraWeightVectors.exists_frame_of_positive_vector {a b : Fin (2 * r + k + 1) → ℂ} (hb : inWb k r b) (hT : 0 < Tz k r b) :
    ∀ m, m ≤ k - 1 → ∃ Bs : Fin m → Fin (2 * r + k + 1) → ℂ, IsFrameOf k r [a, b] Bs := by sorry
