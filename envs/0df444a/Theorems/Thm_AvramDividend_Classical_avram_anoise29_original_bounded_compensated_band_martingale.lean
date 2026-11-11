-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise29_original_bounded_compensated_band_martingale
-- name    : AvramDividend.Classical.avram_anoise29_original_bounded_compensated_band_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:08:32.476533+00:00
-- url     : https://prove2.me/theorems/c321c303-5d30-4a1f-a897-401b15b23ab8
-- title:
--   Original finite signed small-band compensation martingale
-- statement:
--   The actual compensated sum of bounded negative jumps from -1 to the finite cutoff is integrable and a martingale with respect to the original right-continuous filtration. The mark is the actual jump amplitude, not an independent constructed Poisson process.
-- source:
--   Use original finite-simple mark right-continuous conditional expectation, approximate the bounded mark by simple functions and pass in L1 using the original finite-band count moments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise29_original_bounded_compensated_band_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ,
      (∀ t : ℝ≥0, Integrable
        (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) P) ∧
      (∀ s t : ℝ≥0, s ≤ t → ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P
          (fun ω => avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ω =
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n s ω) := by sorry
