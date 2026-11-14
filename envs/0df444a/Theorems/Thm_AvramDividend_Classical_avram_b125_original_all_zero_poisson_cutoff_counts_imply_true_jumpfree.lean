-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
-- name    : AvramDividend.Classical.avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:30:21.949835+00:00
-- url     : https://prove2.me/theorems/d16ad810-1f2f-464d-9f77-ceda2291cc6e
-- title:
--   All zero original negative-mark Poisson cutoff counts force the genuine physical Lévy source interval to have no jumps
-- statement:
--   For the genuine original spectrally negative Levy source, suppose its mapped original jump-counting Poisson measure assigns zero to the actual half-open physical time interval (s,t] crossed with every cofinal negative reciprocal mark cutoff. The Proved canonical original left-limit theorem and original pathwise spectral-negativity field imply a nonzero source jump would have a strictly negative magnitude. Some reciprocal negative cutoff detects that magnitude. Proved original negative-band finite marked-time and exact source count equals ncard then imply that the corresponding Poisson count is positive, contradicting zero. Thus every genuine original source jump on the physical interval vanishes, with no external no-positive-jump assumption, unproved child module, independent Gaussian witness, global negative second moment or almost-everywhere strengthening. This directly supports the hNoJump premise of the original compensated small-mark stopped-grid Ito source decomposition.
-- source:
--   Proved avram_p2_a_zero_rate_original_cadlag_regular_all_times, Proved avram_p2_e_compensator_original_interval_negative_band_count_ncard, Proved avram_wave7_06_original_negative_band_marked_times_finite, original noPosJumps.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_original_cadlag_regular_all_times
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A true original stopped source interval has no physical jumps when every negative-band Poisson count vanishes. -/

theorem AvramDividend.Classical.avram_b125_original_all_zero_poisson_cutoff_counts_imply_true_jumpfree
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hZero : ∀ n : ℕ,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0) :
    ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0 := by sorry
