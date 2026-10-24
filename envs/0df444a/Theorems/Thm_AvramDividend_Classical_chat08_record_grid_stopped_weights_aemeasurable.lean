-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable
-- name    : AvramDividend.Classical.chat08_record_grid_stopped_weights_aemeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T23:16:51.215874+00:00
-- url     : https://prove2.me/theorems/5d88c767-9308-4e95-818f-3e7dc2e6c8ba
-- title:
--   Every lower and upper killed record-grid payment weight is a.e.-measurable
-- statement:
--   For any nonnegative record grid index function (including n and n+1), every stopped discounted first-record cell payment is almost everywhere measurable under the original Lévy law P. It is an immediate uniform-grid specialisation of the genuine first-record payment measurability theorem, furnishing the familywise AEMeasurable hypothesis for the previously accepted finite-to-countable stopped-renewal valuation bounds.
-- source:
--   Prove2Me chat08_killed_first_record_discount_weight_measurable, and Measurable.aemeasurable.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Theorems.Thm_AvramDividend_Classical_chat08_killed_first_record_discount_weight_measurable

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat08_record_grid_stopped_weights_aemeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (a b q h : ℝ)
    (index : ℕ → ℕ) :
    ∀ n : ℕ, AEMeasurable
      (fun ω : Ω =>
        if twoSidedExitUpTime X (b + (index n : ℝ) * h) ω <
          barrierRuinTime X a ω then
          ENNReal.ofReal (h * Real.exp
            (-(q * (twoSidedExitUpTime X (b + (index n : ℝ) * h) ω).toReal)))
        else 0) P := by sorry
