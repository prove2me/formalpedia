-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
-- name    : AvramDividend.Classical.avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T12:04:32.616506+00:00
-- url     : https://prove2.me/theorems/83130961-0b0f-4f0b-9ec5-29cbf6f21b7b
-- title:
--   True BV lower-first killed first-grid scale reward tends to zero almost surely
-- statement:
--   When strict lower ruin precedes upper exit and lies within finite T, the actual first-sampled two-sided stopped killed q-scale reward converges almost surely to zero on original bounded-variation Lévy trajectories. The raw q-scale terminal value is zero by no-downward-creeping, and the historical survival indicator is bounded between zero and one; the result handles positive Wq(0).
-- source:
--   Combines Proved actual BV all-path first-grid convergence ca137f2f, genuine strict lower-first stopped q-scale zero 1f6f4dfd, scale support hW.1, nonnegative first-grid discount-scale rewards and the order squeeze theorem.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_lower_first_capped_terminal_scale_zero_ae
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_tendsto_ae_all_paths

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_lower_first_killed_grid_reward_tendsto_zero_ae
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
      twoSidedExitDownTime X (-x) ω < twoSidedExitUpTime X (a-x) ω →
      (twoSidedExitDownTime X (-x) ω).toNNReal ≤ T →
      Tendsto (fun n =>
        ({η : Ω | ∀ s : ℝ≥0,
          s ≤ min ((K n η : ℝ≥0) * mesh n) T → 0 ≤ x + X.X s η}).indicator
          (fun η => Real.exp (-(q * ((min
              ((K n η : ℝ≥0) * mesh n) T) : ℝ))) *
            W (x + X.X (min ((K n η : ℝ≥0) * mesh n) T) η)) ω)
        atTop (𝓝 0) := by sorry
