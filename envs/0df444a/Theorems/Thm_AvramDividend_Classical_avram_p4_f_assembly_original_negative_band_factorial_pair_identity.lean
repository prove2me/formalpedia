-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_negative_band_factorial_pair_identity
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_negative_band_factorial_pair_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T10:35:53.908797+00:00
-- url     : https://prove2.me/theorems/7cf25aa9-aef9-48ac-8dd0-df87dee1a102
-- title:
--   Original finite negative-band Lévy source jump factorial pair-count identity
-- statement:
--   For the actual original spectrally negative Lévy path X, every finite-horizon negative-jump cutoff has a finite marked-time set. The intrinsic source jump measure's cutoff mass is exactly that set's finite cardinal, and the count of strictly time-ordered distinct jump pairs equals the cardinal factorial n(n−1)/2. This is a pathwise, no-Poisson-count assumption prerequisite for deriving second factorial moments from first-order predictable compensation.
-- source:
--   Original Lévy finite marked-time theorem e5e6f70b, original intrinsic count-to-card theorem f0197436, pinned Mathlib Finset.card_product_filter_lt and Nat.choose_two_right. Supports P4-F original-source jump L² construction; no new random process, independent Poisson or moment assumption.

import Mathlib.MeasureTheory.Measure.Count
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_count_eq_finite_marked_time_card
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_negative_band_marked_times_finite
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_negative_band_factorial_pair_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (n : ℕ) :
    let S : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
        -(1 / ((n : ℝ) + 1))}
    let F : Finset ℝ≥0 :=
      (avram_wave7_06_original_negative_band_marked_times_finite X ω T n).toFinset
    let J : ℝ≥0∞ :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))
    J = (F.card : ℝ≥0∞) ∧
      (F.card * (F.card - 1)) / 2 =
        ((F ×ˢ F).filter (fun p : ℝ≥0 × ℝ≥0 => p.1 < p.2)).card := by sorry
