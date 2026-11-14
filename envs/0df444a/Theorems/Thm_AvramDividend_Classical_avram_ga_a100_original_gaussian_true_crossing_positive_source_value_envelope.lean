-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
-- name    : AvramDividend.Classical.avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:17:56.143204+00:00
-- url     : https://prove2.me/theorems/15a83621-3ada-4386-b4f3-5389b2d0e159
-- title:
--   True original Gaussian source stop-crossing positive cell residual is bounded by stopped value displacement plus full compensator magnitude
-- statement:
--   The true clipped stopping-cell discounted value increment minus any fixed compensation is bounded in positive part by the absolute discounted stopped source value displacement and compensator. The spatial endpoint uses actual X and actual right dividend payment and never evaluates an unclipped source at a potentially negative terminal reserve.
-- source:
--   Original Avram Gaussian positive interior true physical clipping/crossing-cell proof, the proven ga_a72 exact endpoint.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a72_original_gaussian_crossing_cell_clipped_endpoint_eq_stopped_source
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a100_original_gaussian_true_crossing_positive_source_value_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (H : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hs : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hc : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ρ ≤ (i : ℝ≥0) * Δ + Δ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    max (E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (Y (v i))) - H) 0 ≤
      |E ρ| * |w (Y s + (X.X ρ ω - X.X s ω)) - w (Y s)| + |H| := by sorry
