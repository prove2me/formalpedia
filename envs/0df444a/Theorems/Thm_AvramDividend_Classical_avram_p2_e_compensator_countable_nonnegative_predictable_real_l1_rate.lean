-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_nonnegative_predictable_real_l1_rate
-- name    : AvramDividend.Classical.avram_p2_e_compensator_countable_nonnegative_predictable_real_l1_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:24:06.643603+00:00
-- url     : https://prove2.me/theorems/6b0439dc-c4a4-4470-8439-5b5672a26024
-- title:
--   Finite total ν-intensity makes a countable original predictable weighted jump sum real integrable with exact mean
-- statement:
--   On the actual original spectrally negative Lévy path, the countably summed nonnegative past-weighted intrinsic marked jump counts are real integrable if their sum of prescribed ENNReal rates is finite. Their real expectation equals the real conversion of this total rate. The original unconditional ν-rate for each count is an explicit hypothesis; no compensated martingale or replacement Poisson measure is assumed.
-- source:
--   Accepted P2-E countable nonnegative original weighted rate 9d79c515, original count measurability 8146a449, pinned Measurable.tsum, integral_toReal, ae_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_countable_predictable_weighted_rate

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_p2_e_compensator_countable_nonnegative_predictable_real_l1_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℕ → ℝ≥0) (hst : ∀ i, s i ≤ t i)
    (B : ℕ → Set ℝ) (hB : ∀ i, MeasurableSet (B i))
    (W : ℕ → Ω → ℝ≥0∞)
    (hW : ∀ i, Measurable[𝓕 (s i)] (W i))
    (hRate : ∀ i, (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i) ∂P) = (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)))
    (hSumRate : (∑' i, (∫⁻ ω, W i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))) < ⊤) :
    let total : Ω → ℝ≥0∞ := fun ω => ∑' i, W i ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ B i)
    let rateTotal : ℝ≥0∞ := ∑' i, (∫⁻ ω, W i ω ∂P) * (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    Integrable (fun ω => (total ω).toReal) P ∧
      (∫ ω, (total ω).toReal ∂P) = rateTotal.toReal := by sorry
