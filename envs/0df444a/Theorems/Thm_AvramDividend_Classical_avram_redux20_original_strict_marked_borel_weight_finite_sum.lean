-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux20_original_strict_marked_borel_weight_finite_sum
-- name    : AvramDividend.Classical.avram_redux20_original_strict_marked_borel_weight_finite_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:45:36.947551+00:00
-- url     : https://prove2.me/theorems/35828b50-d4bd-4b7d-899c-1ddae2ad729b
-- title:
--   Original strict intrinsic marked-jump integral equals finite sum for any nonnegative measurable mark loss
-- statement:
--   For the genuine spectrally negative Lévy sample path and its finite set of strictly negative jumps before a finite horizon and below a fixed magnitude cutoff, the restricted intrinsic marked-jump integral against any measurable nonnegative mark weight equals the finite sum over those actual jump times. The statement preserves the physical path and cutoffs required by the original Laplace law.
-- source:
--   Generalise the previously Proved original-process strict magnitude finite-sum theorem by applying the exact intrinsic integral-to-jump-sum identity with an arbitrary measurable mark weight, and restrict its countable sum to the already-Proved finite strict cutoff set.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux20_original_strict_marked_borel_weight_finite_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite X ω T k).toFinset
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then g p.2 else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, g (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
