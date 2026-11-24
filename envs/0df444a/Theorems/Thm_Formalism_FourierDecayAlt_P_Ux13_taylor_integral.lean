-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_Ux13_taylor_integral
-- name    : Formalism.FourierDecayAlt.P.Ux13.taylor_integral
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T16:24:40.053439+00:00
-- url     : https://prove2.me/theorems/1a5a924e-f977-4ecd-b35e-fd80836c32de
-- title:
--   Ux13: taylor integral
-- statement:
--   The Ux13 construction uses the taylor integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L14-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/TopCellsOfParts.lean#L14-L46

import Definitions.Def_Formalism_HermitianCurvature_StatementU
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DirectionsInParabolic
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_Block3MulBlocks
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoordinateSizesOfHypotheses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_TopCellsOfParts
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Ux13
open Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

theorem Formalism.FourierDecayAlt.P.Ux13.taylor_integral {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {X W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [CompleteSpace W] {q : ℕ} (H : α → X → W) (ph : α → X → FormalMultilinearSeries ℝ X W)
    (hT : ∀ a, HasFTaylorSeriesUpTo q (H a) (ph a))
    (hmeas : ∀ m ≤ q, ∀ x, AEStronglyMeasurable (fun a => ph a x m) μ)
    (bound : α → ℝ) (hb : Integrable bound μ) (hle : ∀ m ≤ q, ∀ a x, ‖ph a x m‖ ≤ bound a) :
    HasFTaylorSeriesUpTo q (fun x => ∫ a, H a x ∂μ) (fun x m => ∫ a, ph a x m ∂μ) := by sorry
