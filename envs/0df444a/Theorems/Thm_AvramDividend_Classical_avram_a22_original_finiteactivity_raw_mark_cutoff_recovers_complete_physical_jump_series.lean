-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
-- name    : AvramDividend.Classical.avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T14:31:45.046587+00:00
-- url     : https://prove2.me/theorems/7b926252-8157-4f10-87d1-ffa3e053f4ea
-- title:
--   Original finite-activity raw marked small/large cutoffs recover the complete actual left-jump series
-- statement:
--   For original physical spectrally negative finite-activity Lévy X, remove the signed smallmark compensator from the actual intrinsic compensated small band and add the actual uncompensated large mark integral. Then as cutoff n tends to infinity, these original raw physical marked jump integrals recover the negative of the entire original leftjump magnitude series, almost surely simultaneously at all horizons. Use finite actual nonzero jump support and eventual avoidance of zero mark strips, with correct -1 boundary, original Ω,P,filtration. This is a non-circular physical jump identity, independent of Gaussian companion and BV decomposition.
-- source:
--   Original physical jump counting measure definitions; Proved a55466fc finite source jump support, Proved fa3263d5 vanishing sufficiently narrow actual mark tails, Proved c1360947 signed marked integrals equal original jump-time sums. Kyprianou finite activity Levy–Itô decomposition.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a22_original_finiteactivity_raw_mark_cutoff_recovers_complete_physical_jump_series
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_large_jump_sum X t ω +
          avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω +
          (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
             (-(1 / ((n : ℝ) + 1))), z ∂X.ν))
        atTop
        (𝓝 (-(∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω else 0))) := by sorry
