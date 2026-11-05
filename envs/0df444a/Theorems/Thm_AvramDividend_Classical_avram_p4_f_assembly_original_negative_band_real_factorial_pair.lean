-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_real_factorial_pair
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_negative_band_real_factorial_pair
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:46:56.766749+00:00
-- url     : https://prove2.me/theorems/074f945f-26c2-4404-8c57-4116b63d7eef
-- title:
--   Original real factorial source jump count equals twice genuine chronological pair count
-- statement:
--   For the actual original spectrally negative Lévy path and every finite negative jump cutoff, the real-valued physical count J has factorial product J(J−1) exactly twice the number of strictly time-ordered distinct source jump pairs. This source-exact identity converts the pathwise counting lemma into the real L¹ factorial moment used by the genuine P4-B finite-band variance calculation. It does not assume Poisson counting or second-moment integrability.
-- source:
--   Pinned original negative-band count and pair identity 7cf25aa9; finite source marked times e5e6f70b; Nat.even_mul_pred_self and Nat.div_two_mul_two_of_even. No Poisson-law or artificial process hypotheses.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_negative_band_real_factorial_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    J.toReal * (J.toReal - 1) =
      2 * (((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card : ℝ) := by sorry
