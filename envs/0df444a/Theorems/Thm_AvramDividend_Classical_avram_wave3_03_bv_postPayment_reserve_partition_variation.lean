-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_reserve_partition_variation
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_reserve_partition_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T18:30:06.587768+00:00
-- url     : https://prove2.me/theorems/9d284bbb-aa33-417b-a38a-7ab14f8e39d1
-- title:
--   Original BV controlled surplus post-payment partition variation bounded by drift, negative jumps and dividends
-- statement:
--   For the actual standing bounded-variation spectrally negative Levy sample paths, every finite nondecreasing time partition has total post-payment controlled-reserve increment variation bounded by twice positive drift time minus the net original Levy increment plus the actual right-limit dividend increment. This retains all dividend jumps and source process variation.
-- source:
--   Previously Proved original Levy BV partition drift inequality and the actual dividend right-limit path monotonicity, followed by the triangle inequality and telescoping finite sums.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_path_partition_variation_bound_ws01b
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_reserve_partition_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P, ∀ (u : ℕ → ℝ≥0), Monotone u → ∀ n : ℕ,
      (∑ i ∈ Finset.range n,
        |(x + X.X (u (i + 1)) ω - rightLimit D (u (i + 1)) ω) -
          (x + X.X (u i) ω - rightLimit D (u i) ω)|) ≤
      2 * X.drift * ((u n : ℝ) - (u 0 : ℝ)) -
        (X.X (u n) ω - X.X (u 0) ω) +
        (rightLimit D (u n) ω - rightLimit D (u 0) ω) := by sorry
