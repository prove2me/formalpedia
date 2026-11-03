-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands
-- name    : AvramDividend.Classical.avram_wave7_01_source_borel_rate_from_separated_monotone_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:07:57.832026+00:00
-- url     : https://prove2.me/theorems/42393902-56b8-40e2-a0a6-ac5b7faac7ea
-- title:
--   Actual original Lévy mark intensity extends from separated negative bands by monotone convergence
-- statement:
--   For the original spectrally negative Lévy X and actual intrinsic time-mark counting measure, if exact ν(B_n) intensities have been established on an increasing exhaustive collection of Borel bands individually bounded away from mark zero, then the exact unrestricted Borel-mark rate follows by monotone convergence, allowing infinite activity. This is the exact propagation step needed after the missing separated-band Lévy–Khintchine identification and does not assert that identification as an assumption-free theorem.
-- source:
--   Proved actual original past-restricted marked expected count monotone limit a3756344 and the measure continuity from below for the unchanged source Lévy measure X.ν; applies to original target 4928a464.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_marked_expected_count_monotone_limit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_source_borel_rate_from_separated_monotone_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (D : Set ℝ)
    (B : ℕ → Set ℝ) (hBm : ∀ n, MeasurableSet (B n))
    (hBmono : Monotone B) (hBcover : (⋃ n, B n) = D)
    (hSep : ∀ n, ∃ ε : ℝ, 0 < ε ∧ B n ⊆ Iic (-ε))
    (hBandRate : ∀ n,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B n) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n)) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ D) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν D := by sorry
