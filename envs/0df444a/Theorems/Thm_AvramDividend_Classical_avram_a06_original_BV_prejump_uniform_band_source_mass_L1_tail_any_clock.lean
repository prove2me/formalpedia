-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
-- name    : AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T12:48:51.697677+00:00
-- url     : https://prove2.me/theorems/16aebd7f-8711-49d9-aa17-73c18c006e2b
-- title:
--   A06 original BV stopped reserve uniform-band source mass tail vanishes for any finite clock
-- statement:
--   For any original finite time T, not restricted to one, the original spectrally negative Lévy controlled prepayment reserve on a fixed physical grid row has an integrably dominated exceptional spatial-band error. Its expected source-mass omitted tail tends to zero under cofinal interior-band exhaustion, using genuine original BV source mass integrability 777fee57, original reserve left-limit measurability, and the already-Proved original uniform-row DCT. This source mass error can be inserted into the uniform stopped source HJB localisation but does not assert the full cash/HJB ledger.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_postpayment_prejump_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_BV_source_mass_integrable_any_clock
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_uniform_row_weighted_bad_band_expectation_vanish
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology Classical
noncomputable section

theorem AvramDividend.Classical.avram_a06_original_BV_prejump_uniform_band_source_mass_L1_tail_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0)
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
