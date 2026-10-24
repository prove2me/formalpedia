-- Prove2me | Theorems.Thm_AvramDividend_Classical_surviving_stopped_test_aestronglyMeasurable_of_progressive
-- name    : AvramDividend.Classical.surviving_stopped_test_aestronglyMeasurable_of_progressive
-- status  : Open
-- author  : @WillR
-- created : 2026-10-23T23:21:47.225825+00:00
-- url     : https://prove2.me/theorems/2f778d98-8abe-40c2-a45d-00dc5945f25f
-- title:
--   Measurability of a pre-ruin stopped verification function from progressive controlled-reserve measurability
-- statement:
--   If the controlled reserve is progressively measurable, a random horizon is a stopping time, the survival event is measurable, and w is Borel measurable, the stopped reserve at the random horizon is measurable. Applying w and restricting to survival preserves measurability and implies almost-everywhere strong measurability. This is the exact type-level premise required by the already Proved integrability helper; progressive measurability of the specific controlled risk process and stopping nature of its ruin event remain separate process obligations.
-- source:
--   Mathlib.Probability.Process.Stopping measurable_stoppedValue and Mathlib.MeasureTheory.MeasurableSpace.Basic Measurable.ite.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.MeasurableSpace.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.surviving_stopped_test_aestronglyMeasurable_of_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : Measurable w)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0∞)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D))
    (hτ : IsStoppingTime 𝓕 τ)
    (hSurvive : MeasurableSet
      {ω : Ω | τ ω < ruinTime X x D ω}) :
    AEStronglyMeasurable
      (fun ω => if τ ω < ruinTime X x D ω then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) P := by sorry
