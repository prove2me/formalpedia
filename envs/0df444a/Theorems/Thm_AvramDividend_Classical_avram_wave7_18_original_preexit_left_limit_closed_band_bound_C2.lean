-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_preexit_left_limit_closed_band_bound_C2
-- name    : AvramDividend.Classical.avram_wave7_18_original_preexit_left_limit_closed_band_bound_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:48:32.853844+00:00
-- url     : https://prove2.me/theorems/5d3ffd16-9679-44ed-946b-e131a6ccc304
-- title:
--   Original reserve pre-exit left limit remains explicitly bounded by the closed positive C² buffer
-- statement:
--   On the original spectrally negative Lévy reserve Z_s=x+X.X s-rightLimit D s with admissible D and exact ContDiffOn ℝ 2 w on {y|0<y∧ENNReal.ofReal y<C}, suppose 0<t and all Z_s for s<t belong to a closed band [lower,upper], with 0<lower and ENNReal.ofReal y<C throughout. The source original càdlàg reserve theorem supplies a real strict left limit l. Closed-set preservation of limits along 𝓝[<]t yields explicit lower≤l≤upper as well as 0<l, ofReal l<C, and ContDiffWithinAt ℝ 2 w at l. This strengthens the separately Proved original preexit left-limit C² theorem by retaining the quantitative compact-band bound used in predictable/local integrand estimates. No time-zero or simultaneous post-payment jump dominance is asserted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_preexit_left_limit_closed_band_bound_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (ω : Ω) (t : ℝ≥0) (ht : 0 < t)
    (hstay : ∀ s : ℝ≥0, s < t →
      lower ≤ x + X.X s ω - rightLimit D s ω ∧
        x + X.X s ω - rightLimit D s ω ≤ upper) :
    ∃ l : ℝ,
      Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 l) ∧
      (lower ≤ l ∧ l ≤ upper) ∧
      (0 < l ∧ ENNReal.ofReal l < C) ∧
      ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} l := by sorry
