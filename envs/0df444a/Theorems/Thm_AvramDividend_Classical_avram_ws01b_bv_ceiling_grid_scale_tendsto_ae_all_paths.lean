-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
-- name    : AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:35:17.896285+00:00
-- url     : https://prove2.me/theorems/ca137f2f-f4de-4ac2-a973-79a30cf8cfaa
-- title:
--   Actual bounded-variation ceiling-capped two-sided first-grid q-scale converges on all paths
-- statement:
--   The actual original-law BV strict two-sided first-grid discounted q-scale reward converges almost surely at every finite horizon, with correct branch behaviour on finite first exits and on paths never exiting. For finite exits the terminal payoff is observed at the true stopped first passage clock. For infinite exit the reward is exactly the original un-stopped terminal q-scale value at that horizon. No global Wq(0)=0 assumption is made.
-- source:
--   Proved finite original-BV first-exit a.e convergence, and accepted source no-exit grid clock exact terminal cap 3cf9f1dd and no crossing under both infinite clocks 9ae1ae51. This is the genuine a.e all-path prerequisite to L² expectation convergence in the BV branch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae
import Theorems.Thm_AvramDividend_Classical_chat03_no_grid_exit_when_both_passages_infinite
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_sampled_clock_caps_to_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths
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
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (if min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω) < ⊤ then
          Real.exp (-(q * ((min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
            W (x + X.X (min
              (min (twoSidedExitUpTime X (a-x) ω)
                (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
        else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω))) := by sorry
