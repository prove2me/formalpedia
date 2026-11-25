-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_MatrixMultiplicationContinuity_key_bound
-- name    : Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.key_bound
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T03:34:35.048841+00:00
-- url     : https://prove2.me/theorems/6054e630-5e80-47b2-910f-850e9e827045
-- title:
--   Matrix Multiplication Continuity: key bound
-- statement:
--   The Matrix Multiplication Continuity construction uses the key bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L60-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ReproducingFormulaReduction.lean#L60-L79

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

theorem Formalism.FourierDecayAlt.P.MatrixMultiplicationContinuity.key_bound {A S X Y a : ℝ} (hA : 1 ≤ A) (hX : 1 ≤ X) (hY : 1 ≤ Y) (hS0 : 0 < S) (ha : 0 < a)
    (hS : S ≤ A * X * Y) : Y ^ (-a) * A ^ (-a) ≤ X ^ (a / 2) * (Y ^ (-(a / 2)) * S ^ (-(a / 2))) := by sorry
