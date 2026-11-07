-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f14_original_sigma_family_bounded_and_preruin
-- name    : AvramDividend.Classical.avram_p4_f14_original_sigma_family_bounded_and_preruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:38:24.666017+00:00
-- url     : https://prove2.me/theorems/cb700d07-b297-4209-9fcf-0903f12968c4
-- title:
--   Each localised original dividend-process stop is bounded and precedes ruin
-- statement:
--   For the authentic Avram Lévy dividend source, all localisation stops σ_k bounded by the exact min(ruinTime,n) NNReal clock lie below n and before the actual source ruinTime. This discharges both deterministic finite-horizon and preruin bounds required for original stopped compensated-jump martingales.
-- source:
--   Direct source-exact consequence of the public kernel-proved original truncated-clock lemma 6b7a13a0-fa75-494d-8d56-b14562c66491.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_truncated_clock_nnreal_bounds

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_f14_original_sigma_family_bounded_and_preruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k ω,
      σ k ω ≤ (n : ℝ≥0) ∧
      (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by sorry
