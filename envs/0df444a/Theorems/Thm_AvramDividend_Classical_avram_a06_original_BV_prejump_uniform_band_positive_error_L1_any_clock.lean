-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
-- name    : AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:37:42.193638+00:00
-- url     : https://prove2.me/theorems/79f5323e-becb-4e47-bd56-c9301f807442
-- title:
--   A06 original BV positive physical bad-band L1 error vanishes at every finite clock
-- statement:
--   For every finite original spectrally negative Lévy horizon, the positive part of the exact prepayment reserve bad-band error is integrable at each spatial localisation and has vanishing expectation under cofinal interior-band exhaustion. The original BV source mass L1 at arbitrary T is a Proved theorem. Original reserve measurability, finite-row coverage and positive-error dominated convergence are also Proved. This supplies the arbitrary horizon physical error interface, leaving the original stopped cash and HJB ledger.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_positive_error_L1_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    let Err : ℕ → Ω → ℝ := fun k ω =>
      if ∀ i < n + 1,
        (0 < Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
          ∈ Icc (a k) (b k) then (0 : ℝ)
        else |X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|
    (∀ k, Integrable (fun ω => max (Err k ω) 0) P) ∧
    Tendsto (fun k => ∫ ω, max (Err k ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
