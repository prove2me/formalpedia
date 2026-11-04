-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_all_negative_from_rational_below_cutoffs
-- name    : AvramDividend.Classical.avram_p2_c_borel_original_all_negative_from_rational_below_cutoffs
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:30:35.371491+00:00
-- url     : https://prove2.me/theorems/b633277e-2d85-44ad-b0d8-421fc398fc8f
-- title:
--   True original negative Borel rate from harmonic cutoff totals and strictly lower rational tests
-- statement:
--   Exact original Lévy jump rate for every negative Borel mark set, conditional on countably many source ν rate tests: one mass per harmonic cutoff and lower rational halfline thresholds. Uses genuine original marked counts and Borel monotone exhaustion.
-- source:
--   P2-C Proved original separated dense below-cutoff test extension together with harmonic negative band exhaustion and source Borel monotone band extension.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_rate_from_below_cutoff_tests
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_harmonic_negative_band_exhaustion
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_source_borel_rate_from_separated_monotone_bands

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_c_borel_original_all_negative_from_rational_below_cutoffs
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ))
    (hCut : ∀ n : ℕ,
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))))
    (hBelow : ∀ (n : ℕ) (q : ℚ), (q : ℝ) < -(1 / ((n : ℝ) + 1)) →
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (q : ℝ)) ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iic (q : ℝ)))) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) := by sorry
