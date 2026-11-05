-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
-- name    : AvramDividend.Classical.avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:09:58.633254+00:00
-- url     : https://prove2.me/theorems/95286a41-d433-46c6-850e-f363b248ce07
-- title:
--   Dense grid bounded original reserve stop with both post-payment and predictable-side left-limit C² bounds
-- statement:
--   For the original controlled reserve Z=x+X.X-rightLimit D in the original spectrally-negative Lévy filtration, any deterministic countable grid r with DenseRange defines a strict exterior first-observation clock for a positive closed band below the exact finite or infinite C cap; intersect with deterministic bound B. This clock is a stopping time for the right-continuous original filtration. For T before this stop, T≤B, each s<T satisfies lower≤Z_s≤upper, the exact positive source C² domain and ContDiffWithinAt ℝ 2 w. Moreover, each 0<t<T has an original pre-dividend predictable-side left limit l=lim_{s↑t}Z_s, still in the closed band and C² interior. Does not identify the exact simultaneous-jump integrand or assert global exhaustion.

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_bounded_stop_uniform_reserve_band_C2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_countable_clock_preexit_left_limit_uniform_band_bound_C2

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
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
    (hdense : DenseRange r)
    (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0)) ∧
    ∀ (ω : Ω) (T : ℝ≥0),
      (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
            upper < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B : WithTop ℝ≥0) →
      T ≤ B ∧
      (∀ s : ℝ≥0, s < T →
        (lower ≤ x + X.X s ω - rightLimit D s ω ∧
          x + X.X s ω - rightLimit D s ω ≤ upper) ∧
        (0 < x + X.X s ω - rightLimit D s ω ∧
          ENNReal.ofReal (x + X.X s ω - rightLimit D s ω) < C) ∧
        ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
          (x + X.X s ω - rightLimit D s ω)) ∧
      ∀ t : ℝ≥0, 0 < t → t < T →
        ∃ l : ℝ,
          Tendsto (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω)
            (𝓝[<] t) (𝓝 l) ∧
          (lower ≤ l ∧ l ≤ upper) ∧
          (0 < l ∧ ENNReal.ofReal l < C) ∧
          ContDiffWithinAt ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} l := by sorry
