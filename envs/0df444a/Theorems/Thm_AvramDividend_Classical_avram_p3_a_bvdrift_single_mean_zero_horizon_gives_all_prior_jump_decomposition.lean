-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:12:25.486893+00:00
-- url     : https://prove2.me/theorems/b15fec19-8eb1-4f78-9f73-63cf14f26e33
-- title:
--   One original BV residual mean-zero horizon yields pure-jump identity on every earlier time
-- statement:
--   For the same original bounded-variation spectrally negative Lévy process and Standing assumptions, one actual intrinsic-jump residual integrability and zero-mean identity at a single finite horizon T implies on one full-probability event the exact source drift-minus-all-negative-left-jumps path identity simultaneously for every t≤T. The result exploits the original residual's nonnegativity and monotonicity, and is explicitly conditional on the uncompensated source first-moment equality rather than asserting that equality from BV alone.
-- source:
--   Avram P3-A single-horizon consolidation of canonically Proved source residual monotonicity 93ee4a8c and exact fixed-horizon expectation criterion b9ebb78a. It strengthens countable-integer-horizon conditional formulations on finite intervals while retaining the original probability measure and filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_standing_bv_zero_anchored_intrinsic_source_with_nonnegative_downward_residual
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04a_actual_BV_fixed_horizon_intrinsic_residual_mean_zero_implies_pure_jump

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- An original-source mean-zero residual at one horizon removes the entire
monotone residual on all earlier physical times, almost surely. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_single_mean_zero_horizon_gives_all_prior_jump_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hIntegrable : Integrable (fun ω : Ω =>
      ((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) P)
    (hMeanZero : (∫ ω : Ω,
      (((T : ℝ) * X.drift - X.X T ω) -
        (∑' (v : ℝ≥0),
          if 0 < v ∧ v ≤ T then
            ENNReal.ofReal (Function.leftLim
              (fun z : ℝ≥0 => X.X z ω) v - X.X v ω)
          else 0).toReal) ∂P) = 0) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t ≤ T →
      X.X t ω = (t : ℝ) * X.drift -
        (∫⁻ p,
          (if 0 < p.1 ∧ p.1 ≤ t then ENNReal.ofReal (-p.2) else 0) ∂
          ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
            X.X u ω - Function.leftLim
              (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim
                (fun v : ℝ≥0 => X.X v ω) u)))).toReal := by sorry
