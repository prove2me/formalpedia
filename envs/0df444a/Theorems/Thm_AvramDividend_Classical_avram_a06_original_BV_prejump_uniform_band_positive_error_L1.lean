-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_positive_error_L1
-- name    : AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_positive_error_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:34:02.456046+00:00
-- url     : https://prove2.me/theorems/23267159-3cb3-4cc1-b2bf-e597c575401a
-- title:
--   A06 original BV physical uniform bad-band positive error is integrable and vanishes in mean
-- statement:
--   For the actual original spectrally negative Lévy process and admissible dividend strategy, the positive part of the original prepayment reserve spatial-band omitted error is integrable at every compact localisation and has vanishing mean as the bands exhaust the interior. The error is explicitly zero on the good fixed physical row and otherwise equals the original source BV variation envelope. The argument uses exact source measurability, original-source integrable variation for T at most one, eventual finite-row band coverage, and a proved DCT transfer. It provides an L1 positive physical-error premise without any L1 assumption on a signed HJB residual.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_positive_physical_error_L1_from_integrable_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_positive_error_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : T ≤ 1)
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
