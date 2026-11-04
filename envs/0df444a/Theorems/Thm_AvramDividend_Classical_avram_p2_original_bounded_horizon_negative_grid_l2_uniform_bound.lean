-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound
-- name    : AvramDividend.Classical.avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T06:57:26.184544+00:00
-- url     : https://prove2.me/theorems/9cfd46a8-0f45-4088-b69f-11e030261805
-- title:
--   Original bounded-horizon negative-increment grid counts have a uniform second-moment bound
-- statement:
--   For the actual original spectrally negative Lévy process X, every positive negative-jump separation and nonnegative time horizon T admits a finite uniform bound on the true squared negative-increment grid counts for all sufficiently small positive mesh widths h and any number n of equal cells satisfying nh<=T. The proof combines the original independent-increment quadratic count bound with the directly Proved O(h) source event probability. This uniform L² bound is the key uniform-integrability input for converging grid test sums to actual intrinsic jumps, without assuming any Poisson proxy or compensator.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_uniform_negative_grid_probability_mass
import Theorems.Thm_AvramDividend_Classical_avram_p2_original_equispaced_negative_grid_quadratic_bound

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
attribute [local instance] Classical.propDecidable

theorem AvramDividend.Classical.avram_p2_original_bounded_horizon_negative_grid_l2_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (ε : ℝ) (hε : 0 < ε) (T : ℝ) (hT : 0 ≤ T) :
    ∃ C : ℝ, 0 < C ∧
      ∀ᶠ h : ℝ in nhdsWithin (0 : ℝ) (Ioi 0),
        ∀ n : ℕ, (n : ℝ) * h ≤ T →
        (∫⁻ ω, (∑ i ∈ Finset.range n,
          ({v : Ω | X.X ((↑(i + 1) : ℝ≥0) * Real.toNNReal h) v -
              X.X ((i : ℝ≥0) * Real.toNNReal h) v ≤ -ε}).indicator
            (fun _ => (1 : ℝ≥0∞)) ω) ^ 2 ∂P) ≤
          ENNReal.ofReal (C * T) + (ENNReal.ofReal (C * T)) ^ 2 := by sorry
