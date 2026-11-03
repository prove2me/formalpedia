-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_future_increment_L1_integrable_equal_mean
-- name    : AvramDividend.Classical.avram_wave7_06_original_future_increment_L1_integrable_equal_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T15:50:29.945956+00:00
-- url     : https://prove2.me/theorems/a75a0084-7c03-4c3a-ae5b-d808b42f30c9
-- title:
--   Original future Lévy increments preserve L¹ integrability and expected value
-- statement:
--   Whenever X_t is integrable on the original Lévy space, the shifted future increment X_(s+t)-X_s is integrable and has the same expectation. The result is an exact original-filtration L¹ moment transport from stationary increments.
-- source:
--   W7-06 original future increment L¹ moment interface toward marked-cell compensation and expectation limit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_06_original_future_increment_L1_integrable_equal_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s t : ℝ≥0)
    (hInt : Integrable (X.X t) P) :
    Integrable (fun ω => X.X (s + t) ω - X.X s ω) P ∧
    (∫ ω, (X.X (s + t) ω - X.X s ω) ∂P) =
      ∫ ω, X.X t ω ∂P := by sorry
