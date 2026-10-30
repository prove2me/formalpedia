-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_limit_aestrongly_measurable
-- name    : AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_limit_aestrongly_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:47:59.093166+00:00
-- url     : https://prove2.me/theorems/b9799867-519c-4088-8a3f-0cdbf3496c80
-- title:
--   Original BV two-sided stopped finite-horizon q-scale limit is a.e. measurable
-- statement:
--   The full original BV ceiling-capped first-grid q-scale payoff limit is almost everywhere strongly measurable, including finite strict exits and paths with no strict exit, without a zero-scale-at-origin assumption. Measurability comes from the genuine sampled stopped q-scale rewards and their a.e convergence, allowing the pinned L² expectation convergence theorem to apply.
-- source:
--   Specialisation of Proved generic measurable bounded-grid reward lemma and measurability of limits, with the genuine BV all-path ceiling-grid convergence. All source clocks use actual original Levy filtration and bounded sampled hitting indices.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_clipped_grid_clock_bounded
import Theorems.Thm_AvramDividend_Classical_chat03_monotone_clock_reindexed_filtration
import Theorems.Thm_AvramDividend_Classical_chat03_grid_stopped_scale_reward_measurable

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_limit_aestrongly_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    AEStronglyMeasurable (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) P := by sorry
