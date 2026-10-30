-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:05:29.029767+00:00
-- url     : https://prove2.me/theorems/3a308ac9-74cb-40ca-836b-7e04e16b1089
-- title:
--   Actual BV upper-first killed ceiling-grid q-scale reward converges to strict upper-exit payoff
-- statement:
--   For actual bounded-variation spectrally negative Lévy paths with upper first passage strictly before the time horizon, the full-history killed sampled stopped q-scale payoff converges almost surely to the real discounted q-scale reward at the genuine upper first-exit clock. It uses original no-positive-jump crossing law, actual capped-grid clock convergence and eventual continuous-history survival.
-- source:
--   Combines original-law stopped-grid q-scale convergence ca137f2f, finite strict first-exit GLB bb38e95f and true upper-first mesh survival 4b15e831; eventual equality of killed and raw grid payoffs.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_upper_first_ceiling_grid_survival_eventually
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_finite_two_sided_min_isGLB
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_upper_first_killed_grid_reward_tendsto_ae
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
      twoSidedExitUpTime X (a-x) ω < twoSidedExitDownTime X (-x) ω →
      (twoSidedExitUpTime X (a-x) ω).toNNReal < T →
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝 (Real.exp (-(q * ((twoSidedExitUpTime X (a-x) ω).toNNReal : ℝ))) *
          W (x + X.X (twoSidedExitUpTime X (a-x) ω).toNNReal ω))) := by sorry
