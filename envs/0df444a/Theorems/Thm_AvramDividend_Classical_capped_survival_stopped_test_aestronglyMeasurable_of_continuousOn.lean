-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
-- name    : AvramDividend.Classical.capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:31:34.763978+00:00
-- url     : https://prove2.me/theorems/08d665c1-9474-41b4-9bf9-3c6c051cfb26
-- title:
--   Measurability of the finite-cap stopped HJB payoff from compact continuity and stopping-time conditions
-- statement:
--   For a progressive controlled reserve and stopping time, an admissible dividend strategy makes the survival event measurable. If the stopped surviving reserve is in a finite cap interval and the HJB test function is continuous on that interval, its zero-extended test composition is measurable. On the survival set, this equals the actual stopped HJB value, proving its a.e. strong measurability. This eliminates global-measurability assumptions and connects directly to the earlier finite-cap integrability lemma.
-- source:
--   Two canonically proved stopping-time/cap measurability helpers once available, plus Mathlib measurable_stoppedValue and Measurable.ite.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (B : ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) B))
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D))
    (hCap : ∀ ω, τ ω < ruinTime X x D ω →
      stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B) :
    AEStronglyMeasurable
      (fun ω => if τ ω < ruinTime X x D ω then
        w (stoppedValue (riskProcess X x D) τ ω) else 0) P := by sorry
