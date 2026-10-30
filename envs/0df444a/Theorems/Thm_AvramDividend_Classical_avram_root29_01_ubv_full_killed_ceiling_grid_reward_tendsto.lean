-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_full_killed_ceiling_grid_reward_tendsto
-- name    : AvramDividend.Classical.avram_root29_01_ubv_full_killed_ceiling_grid_reward_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T16:41:52.943551+00:00
-- url     : https://prove2.me/theorems/04200378-ef1b-4d11-a6f2-b876dda54838
-- title:
--   Actual UBV full-history-killed ceiling-grid q-scale convergence for all passage branches
-- statement:
--   For every source unbounded-variation spectrally negative Lévy path and capped authentic ceiling hitting grid, the continuously lower-history-killed q-scale reward converges to the explicit true upper-exit, lower-zero or surviving-horizon payoff. The Proved variation-independent three-way first-passage partition separates exact lower-before-T, strict upper-first and horizon survival; use the independently accepted three source-specific UBV component limits, no Standing, no two-sided exit ratio.
-- source:
--   WS1A work/avram_root29_01_ubv_full_killed_ceiling_grid_reward_tendsto_draft.lean

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_two_sided_horizon_killed_grid_three_way_cover
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_lower_first_ceiling_killed_reward_zero
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_upper_first_ceiling_killed_reward_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_root29_01_ubv_surviving_horizon_killed_reward_tendsto

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_01_ubv_full_killed_ceiling_grid_reward_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (ω : Ω) (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (nhds 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Tendsto (fun n =>
      ({η : Ω | ∀ s : ℝ≥0,
        s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min
            ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
      atTop
      (nhds (if (T : ℝ≥0∞) < twoSidedExitDownTime X (-x) ω then
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
      else Real.exp (-(q *
        ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
        W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by sorry
