-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_isClosed_UH
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.isClosed_UH
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:41:00.507326+00:00
-- url     : https://prove2.me/theorems/fc572c3b-aa71-45e2-94b7-c757ddf692a6
-- title:
--   Matrix Multiplication Continuity: is Closed UH
-- statement:
--   The Matrix Multiplication Continuity construction uses the is Closed UH property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L35-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L35-L38

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction
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
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity
open Formalism.FourierDecayAlt.ThreeDimData
variable {k r : ℕ}

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.isClosed_UH : IsClosed (Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) : Set (Mx k r)) := by sorry
