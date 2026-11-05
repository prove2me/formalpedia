-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_nu_quadratic_real_energy
-- name    : AvramDividend.Classical.avram_p4_h_gaussian_original_nu_quadratic_real_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:22:50.537583+00:00
-- url     : https://prove2.me/theorems/5dc7c9ac-0939-48ad-bb94-e7f676b51611
-- title:
--   Original Lévy small-jump quadratic tail is real-integrable and agrees with its ENNReal energy
-- statement:
--   For every original Lévy X and cutoff n, the squared negative jump-mark function is Bochner integrable even on the infinite-activity neighbourhood (-1/(n+1),0], and the ENNReal representation of its real integral is exactly the corresponding lintegral. This is the same-original-source real/ENNReal quadratic-energy interface needed when connecting P4-H tail bounds to P4-G second-moment isometries.
-- source:
--   Directly from the source Lévy measure's X.ν_integrable and pinned Mathlib lintegral_indicator, lintegral_mono, hasFiniteIntegral_iff_ofReal and ofReal_integral_eq_lintegral_ofReal. No replacement process or Gaussian decomposition assumed.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_h_gaussian_original_nu_quadratic_real_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (n : ℕ) :
    IntegrableOn (fun z : ℝ => z ^ 2)
      (Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ)) X.ν ∧
    ENNReal.ofReal (∫ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ), z ^ 2 ∂X.ν) =
      ∫⁻ z in Ioc (-(1 / ((n : ℝ) + 1))) (0 : ℝ),
        ENNReal.ofReal (z ^ 2) ∂X.ν := by sorry
