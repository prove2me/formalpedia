-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_isClosed_UW
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.isClosed_UW
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:58:50.126136+00:00
-- url     : https://prove2.me/theorems/b1ff957d-b8cc-5898-bc4b-41e86772ac20
-- title:
--   Matrix Multiplication Continuity: is Closed UW
-- statement:
--   The Matrix Multiplication Continuity construction uses the is Closed UW property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L40-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L40-L51

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ContinuousMulMt
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SigmaContOn
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ReproducingFormulaReduction
import Theorems.Thm_Formalism_FourierDecayAlt_P_B7_isClosed_UW

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

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.isClosed_UW (z : Fin (2 * r + k + 1) → ℂ) : IsClosed (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) := by sorry
