-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_full_killed_ceiling_grid_reward_tendsto_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_full_killed_ceiling_grid_reward_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:45:42.586081+00:00
-- url     : https://prove2.me/theorems/06071ec4-2cd3-4a1f-9008-5f4149497a6a
-- title:
--   Actual BV killed stopped-grid discounted scale reward converges a.e. with all three source clock regimes
-- statement:
--   For the actual spectrally negative Lévy reserve with bounded variation and a true q-scale function, every capped sampled first-exit clock has a full-history killed reward that converges almost surely to the exact source stopped payoff. The three exhaustive cases are horizon before ruin, lower-first ruin giving zero, and upper-first exit giving the genuine discounted q-scale boundary reward.
-- source:
--   Combine the accepted original-clock killed-horizon three-way cover with separately verified true lower-first, upper-first and surviving-horizon source convergence. The lower branch uses strict BV undershoot; no false W(0)=0 premise.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_surviving_horizon_killed_grid_scale_tendsto_ae

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_full_killed_ceiling_grid_reward_tendsto_ae
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
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝
          (if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
            if min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω) < ⊤ then
              Real.exp (-(q * ((min (min
                (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
                W (x + X.X (min (min
                  (twoSidedExitUpTime X (a-x) ω)
                  (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
            else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)
          else if twoSidedExitDownTime X (-x) ω <
                  twoSidedExitUpTime X (a-x) ω then 0
          else Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
            W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by sorry
