-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_ChartIntegralLocal_ck_at_of_chart
-- name    : Formalism.FourierDecayAlt.P.ChartIntegralLocal.ck_at_of_chart
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T16:31:08.395521+00:00
-- url     : https://prove2.me/theorems/0c53b905-ccd1-44f7-a32c-d4f45bf3bdf1
-- title:
--   Chart Integral Local: ck at of chart
-- statement:
--   The Chart Integral Local construction uses the ck at of chart property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChartIntegralLocal.lean#L151-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/ChartIntegralLocal.lean#L151-L180

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PhiBoundPartsOfRadicalParametrisation
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChartIntegralLocal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix MeasureTheory Filter Topology
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.ChartIntegralLocal
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B4 Formalism.FourierDecayAlt.P.Ux10
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
  {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

theorem Formalism.FourierDecayAlt.P.ChartIntegralLocal.ck_at_of_chart {F : Mat k r → E} {mm : ℕ} {g0 : Mat k r} (hg0 : g0 ∈ GV k r) {δ : ℝ} (hδ : 0 < δ)
    (hAL : ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) (fun Y => F (chart g0 Y)) (Metric.ball 0 δ)) :
    ∃ (U : Set (Mat k r)) (F' : Mat k r → E), IsOpen U ∧ g0 ∈ U ∧
      ContDiffOn ℝ ((mm : ℕ) : WithTop ℕ∞) F' U ∧ ∀ g ∈ U, g ∈ GV k r → F g = F' g := by sorry
