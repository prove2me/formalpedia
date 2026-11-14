-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_standing_BV_actual_cofinal_halfband_discounted_negative_mark_budget_eventually_below_drift
-- name    : AvramDividend.Classical.avram_bva_a22_original_standing_BV_actual_cofinal_halfband_discounted_negative_mark_budget_eventually_below_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:04:32.387044+00:00
-- url     : https://prove2.me/theorems/30c7c7b9-9be7-46f3-a1fc-265c3293f9c8
-- title:
--   Actual standing BV source half-band a_n/2 has negative Levy truncated first-moment and discount budget eventually below physical drift without choosing a rate
-- statement:
--   Under exactly the original Avram standing spectrally negative Levy bounded variation process and its strictly positive discounted verification problem, let a_n,b_n be ANY user-supplied positive spatial bands with a_n<=2, a_n<=b_n, half-width interior inclusion and eventual cofinal coverage of every strict interior reserve. Prove the actual ORIGINAL half-band width a_n/2 satisfies q*a_n/2 + integral over the true negative Levy measure of min(a_n/2,-z) < X.drift eventually along the same original row index, without any chosen spatial rate, nesting or fast diagonal. The original cofinal hypothesis forces a_n→0; original Standing BV implies positive drift; the Proved arbitrary shrinking spatial first-moment theorem then yields the genuine source budget. This is the precise deterministic near-zero jump and discount compensation estimate needed by the canonical BV C1 positive spatial error in BVA96.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_bv_standing_drift_pos
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_arbitrary_cofinal_positive_spatial_lower_band_tendsto_zero_without_rate
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_BV_any_shrinking_spatial_width_eventual_positive_physical_drift_after_negative_mark_budget
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bva_a22_original_standing_BV_actual_cofinal_halfband_discounted_negative_mark_budget_eventually_below_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (C : ℝ≥0∞) (hC : 0 < C)
    (a b : ℕ → ℝ) (ha : ∀ n, 0 < a n)
    (ha2 : ∀ n, a n ≤ 2) (hab : ∀ n, a n ≤ b n)
    (hinside : ∀ n, Icc (a n / 2) (b n) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    ∀ᶠ n : ℕ in atTop,
      q * (a n / 2) +
        (∫ z in Iio (0 : ℝ), min (a n / 2) (-z) ∂X.ν) < X.drift := by sorry
