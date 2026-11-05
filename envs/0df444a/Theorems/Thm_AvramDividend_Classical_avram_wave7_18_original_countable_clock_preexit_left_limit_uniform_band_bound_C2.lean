-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
-- name    : AvramDividend.Classical.avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:56:23.60908+00:00
-- url     : https://prove2.me/theorems/51095652-b0df-4e67-8cde-4a37965c1681
-- title:
--   Original pre-exit countable clock bounds the strict reserve left limit inside the closed C² band
-- statement:
--   Take the exact original Lévy reserve Z_t=x+X.X t-rightLimit D t in the original filtration and its right-cofinal countable deterministic strict-exterior observation clock for a closed positive band [lower,upper], with full band under ENNReal cap C. Preserve the source ContDiffOn ℝ 2 w {y|0<y∧ENNReal.ofReal y<C}. Whenever 0<t<T≤the clock, the true left-hand reserve limit l=lim_(s↑t) Z_s exists and obeys the quantitative bound lower≤l≤upper, positivity and cap membership, and ContDiffWithinAt ℝ 2 w in the exact interior domain. The proof imports already Proved right-continuous grid detection and clock-prefix band equivalence, then the new original left-limit closed-band lemma after it is Proved. This provides the stopped predictable-side boundedness W7-08 needs, while keeping simultaneous postpayment jumps separate.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) →
      ∀ t : ℝ≥0, 0 < t → t < T →
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
            (𝓝[<] t) (𝓝 l) ∧
          (lower ≤ l ∧ l ≤ upper) ∧
          (0 < l ∧ ENNReal.ofReal l < C) ∧
          ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} l := by sorry
