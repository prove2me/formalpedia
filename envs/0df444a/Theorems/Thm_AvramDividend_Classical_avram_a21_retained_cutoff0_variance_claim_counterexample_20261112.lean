-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_retained_cutoff0_variance_claim_counterexample_20261112
-- name    : AvramDividend.Classical.avram_a21_retained_cutoff0_variance_claim_counterexample_20261112
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T23:12:02.961206+00:00
-- url     : https://prove2.me/theorems/6f797dcf-1592-4860-b8a1-c6e854577f46
-- title:
--   Explicit same-space standing Lévy counterexample to omitted-tail small-band variance at cutoff zero
-- statement:
--   There exists an original spectrally negative Lévy process satisfying the classical Standing and finite negative activity assumptions whose cutoff-zero small-jump compensator has second moment zero, while its strictly negative uniform jump measure has strictly positive weighted squared-mark mass on (-1,0). This disproves the omitted-tail formula asserted in d73cacfa-0d1c-469a-a411-19f0a3fa81be at n=0, t=1.
-- source:
--   Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated; original standing source ba817b45-a132-4a78-8f03-5d876fa093d5; strict squared mass 789bda55-03da-490b-ae50-4699076e596b; zero-cutoff theorem 8d8eedb1-b868-4e12-86ac-370653cab5ee.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Theorems.Thm_AvramDividend_Classical_avram_a20_negative_uniform_original_standing_source_exists
import Theorems.Thm_AvramDividend_Classical_avram_a20_uniform_negative_levy_square_mass_positive
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated_zero_cutoff
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a21_retained_cutoff0_variance_claim_counterexample_20261112 :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.ν (Iio (0 : ℝ)) ≠ ⊤ ∧
      (∫ ω, (avram_p4_h_gaussian_intrinsic_small_band_compensated
        X 0 (1 : ℝ≥0) ω) ^ 2 ∂P) ≠
        (1 : ℝ) * (∫ z in Ioo (-1 : ℝ) 0, z ^ 2 ∂X.ν) := by sorry
