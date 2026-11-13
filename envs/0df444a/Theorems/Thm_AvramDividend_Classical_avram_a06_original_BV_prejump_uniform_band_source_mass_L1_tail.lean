-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail
-- name    : AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:22:16.1702+00:00
-- url     : https://prove2.me/theorems/a72709e6-622f-4556-bfc9-2eda391dd3f4
-- title:
--   A06 original Lévy prepayment uniform-row bad-band L1 error vanishes under genuine source mass
-- statement:
--   For actual original spectrally negative Lévy process X under its standing BV hypotheses, any original admissible dividend D, every fixed physical mesh row, and any cofinal compact spatial interior bands, prove vanishing expected source mass supported on missed interior-band coordinates. The actual envelope is absolute drift times horizon plus absolute compensated original source variation, whose integrability follows from the separately Proved original-source BV theorem for T at most one. Exact joint prepayment reserve measurability comes from the Proved original X/D left-limit theorem. No signed HJB residual B integrability is assumed, and the result is ready for physical finite-horizon grid localisation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (hT : T ≤ 1)
    (u : ℕ → ℕ → ℝ≥0) (n : ℕ)
    (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k)) :
    Tendsto (fun k : ℕ =>
      ∫ ω, (if ∀ i < n + 1,
        (0 < Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i) ∧
          ENNReal.ofReal (Function.leftLim
            (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)) < C) →
        Function.leftLim
          (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) (u n i)
          ∈ Icc (a k) (b k) then (0 : ℝ)
        else |X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
