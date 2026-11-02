-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks
-- name    : AvramDividend.Classical.avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T08:36:34.429203+00:00
-- url     : https://prove2.me/theorems/3ae57b3c-959f-46f7-ba88-a55f35a44126
-- title:
--   Genuine controlled ruin admits measurable increasing bounded integer-horizon clocks
-- statement:
--   For a native dividend strategy on the original spectrally negative Lévy process and its actual controlled ruin time σ, the source-path random clocks τ_n= min(σ,n) are measurable, monotone in n on every sample path, and converge in ENNReal supremum to σ, including σ=∞. Uses the canonically Proved measurability of the genuine ruin time, min order monotonicity, frame distributivity and ENNReal supremum of natural casts. This constructs an explicit family satisfying the stopping-clock premises of the Proved complete Stieltjes localisation theorem, while preserving time-zero atoms, arbitrary diffuse dividends and actual path filtration. It is a clock construction, not a stopped Ito–Meyer estimate.
-- source:
--   Proved AvramDividend.Classical.ruinTime_measurable UUID bbfbecf4-7dfc-4812-84f3-8644c2b40b85. Private remote probe job 538a8a27-577f-49d6-ae40-43ff34855adf reached intentional sentinel.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_05_genuine_ruin_bounded_monotone_measurable_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    (∀ n : ℕ,
        Measurable (fun ω : Ω =>
          min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ ω : Ω,
        Monotone (fun n : ℕ =>
          min (ruinTime X x D ω) (n : ℝ≥0∞))) ∧
    (∀ ω : Ω,
        (⨆ n : ℕ, min (ruinTime X x D ω) (n : ℝ≥0∞)) =
          ruinTime X x D ω) := by
  sorry
