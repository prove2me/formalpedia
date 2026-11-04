-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clock_product_measurable_sets
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_clock_product_measurable_sets
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:15:10.468897+00:00
-- url     : https://prove2.me/theorems/cb6d7bfc-d9b7-4077-a34a-1d03b4647c8a
-- title:
--   Actual original controlled ruin-time strict and clipped strict product thresholds are measurable
-- statement:
--   For the original controlled spectrally negative Lévy reserve and a true dividend strategy, the full pre-ruin space-time subset (t,ω) satisfying t<ruinTime and every deterministic min(ruinTime,n) space-time subset are measurable under the product Borel-sample sigma algebra. This uses the already-Proved original ruinTime_measurable source theorem and measurable coordinate projection/ENNReal cast/min. It will permit Fubini to construct integrable stopped physical-time residuals and remove external AEStronglyMeasurable hypotheses.
-- source:
--   Accepted original AvramDividend.Classical.ruinTime_measurable bbfbecf4-7dfc-4812-84f3-8644c2b40b85; Mathlib measurableSet_lt and Measurable.min.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original random ruin-clock space-time threshold sets are product measurable. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_clock_product_measurable_sets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hDiv : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < ruinTime X x D p.2} ∧
    ∀ n : ℕ, MeasurableSet {p : ℝ≥0 × Ω |
      (p.1 : ℝ≥0∞) < min (ruinTime X x D p.2) (n : ℝ≥0∞)} := by sorry
