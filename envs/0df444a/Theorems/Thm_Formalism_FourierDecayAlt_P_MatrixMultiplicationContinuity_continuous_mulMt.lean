-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_continuous_mulMt
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.continuous_mulMt
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:18:24.748798+00:00
-- url     : https://prove2.me/theorems/83dddaa7-26a0-4d48-9aaa-f95d1f414663
-- title:
--   Matrix Multiplication Continuity: continuous mul Mt
-- statement:
--   The Matrix Multiplication Continuity construction uses the continuous mul Mt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ContinuousMulMt.lean#L14-L19

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

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.continuous_mulMt {k r : ℕ} :
    Continuous (fun q : Formalism.QuantumDeterminants.Mt k r × Formalism.QuantumDeterminants.Mt k r => mulMt q.1 q.2) := by sorry
