-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_uwset_eq
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uwset_eq
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:00.22485+00:00
-- url     : https://prove2.me/theorems/109b88e7-a049-47a7-8baa-491544fc4db9
-- title:
--   Matrix Multiplication Continuity: uwset eq
-- statement:
--   The Matrix Multiplication Continuity construction uses the uwset eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L115-L115
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L115-L115

import Definitions.Def_Formalism_HermitianCurvature_BesselNonvanishingReduction
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_HighestWeightUniqueness_FrameInvMulVecNegativeVector
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BesselNeZeroOfCyclicOrbit
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.uwset_eq (z : Fin (2 * r + k + 1) → ℂ) : Formalism.QuantumDeterminants.UWset k r z = PI.UpqRep.UWset k r z := by sorry
