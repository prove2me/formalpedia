-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum
-- name    : AvramDividend.Classical.avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:35:35.622206+00:00
-- url     : https://prove2.me/theorems/dcb42883-7bb0-4412-a1f3-67c5ad26debd
-- title:
--   Original intrinsic strict-cutoff jump magnitude integral equals actual finite physical mark sum
-- statement:
--   On the unchanged original spectrally negative Levy path, the intrinsic marked-measure integral of the exact strict-cutoff negative jump magnitudes equals the finite sum over its actual selected strict negative jump times, with the same (0,T] clock and all sample paths. This identifies the canonical Laplace source variable with a physical finite sum.
-- source:
--   Use the Proved original intrinsic counting-measure-to-jump-tsum identity e4542c93 with the measurable strict cutoff kernel, reduce its support using Proved original strict marked-time finiteness e19c4927, and rewrite the unrestricted ENNReal tsum as the finite source mark-magnitude sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_redux19_original_strict_intrinsic_marked_magnitude_finite_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ≥0) (k : ℕ) :
    let J : Set ℝ≥0 := {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u <
        -(1 / ((k : ℝ) + 1))}
    let S : Finset ℝ≥0 :=
      (AvramDividend.Classical.avram_redux19_original_strict_negative_marked_times_finite
        X ω T k).toFinset
    (∫⁻ p : ℝ≥0 × ℝ,
      if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then ENNReal.ofReal (-p.2) else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u,
            X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
    ∑ u ∈ S, ENNReal.ofReal (-(X.X u ω -
      Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by sorry
