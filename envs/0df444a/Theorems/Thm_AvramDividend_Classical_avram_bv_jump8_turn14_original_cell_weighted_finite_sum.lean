-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_original_cell_weighted_finite_sum
-- name    : AvramDividend.Classical.avram_bv_jump8_turn14_original_cell_weighted_finite_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T14:46:01.044585+00:00
-- url     : https://prove2.me/theorems/35add7e6-1a10-497f-86f5-cbb040b27edd
-- title:
--   Original intrinsic negative marked loss on any half-open cell equals the finite physical jump sum
-- statement:
--   For any original spectrally negative Lévy sample path, nonnegative times s,t, strict negative mark cutoff k and measurable nonnegative weight g, the intrinsic marked-jump integral over the half-open cell (s,t] is exactly the finite sum over the same physical jump times. The original source process, filtration and left-limit mark are unchanged.
-- source:
--   Direct adaptation of the accepted arbitrary-mark finite-sum theorem 35828b50, applying the intrinsic marked-jump integral-to-tsum identity e4542c93 and restricting the tsum to the existing finite negative cutoff jump set on (0,t], filtered to the actual cell (s,t]. Needed to identify the per-cell factors in a657c8d2 with bounded shifted path functionals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_redux19_original_strict_negative_marked_times_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_intrinsic_lintegral_eq_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_jump8_turn14_original_cell_weighted_finite_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (s t : ℝ≥0) (k : ℕ)
    (g : ℝ → ℝ≥0∞) (hg : Measurable g) :
    let S : Finset ℝ≥0 :=
      (avram_redux19_original_strict_negative_marked_times_finite X ω t k).toFinset.filter
        (fun u => s < u)
    (∫⁻ p : ℝ≥0 × ℝ,
      if s < p.1 ∧ p.1 ≤ t ∧ p.2 < -(1 / ((k : ℝ) + 1))
      then g p.2 else 0
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) =
      ∑ u ∈ S, g (X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) := by sorry
