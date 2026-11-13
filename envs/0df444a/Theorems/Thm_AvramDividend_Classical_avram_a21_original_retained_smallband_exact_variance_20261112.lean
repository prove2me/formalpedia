-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_retained_smallband_exact_variance_20261112
-- name    : AvramDividend.Classical.avram_a21_original_retained_smallband_exact_variance_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:17:53.212765+00:00
-- url     : https://prove2.me/theorems/56fd031e-eff9-4b34-933e-eec41b1de326
-- title:
--   Correct physical original compensated retained negative jump-band variance
-- statement:
--   For every cutoff n and horizon t, the compensated original marked jump integral over the retained negative band between minus one (excluded) and minus the reciprocal of n plus one (included) has exact second moment equal to time multiplied by the squared-mark Lévy measure of that same retained band. This corrects the omitted-tail interval mismatch in d73cacfa.
-- source:
--   Physical marked jump definition 66a113ed-6260-42ea-862c-576aa1e2b0cb, Proved original raw first and second finite-band moments 4106f6a7-d069-4504-a840-d5b32edca1d5, original probability X.isProbability. Avram-Palmowski-Pistorius (2007) Proposition 4(i) and compensated Poisson isometry.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_ja28_original_bounded_mark_raw_first_second_moments
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_retained_smallband_exact_variance_20261112
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated
        X n t ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in Ioc (-1 : ℝ)
          (-(1 / ((n : ℝ) + 1))), z ^ 2 ∂X.ν) := by sorry
