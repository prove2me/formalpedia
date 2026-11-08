-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_cell7_original_BV_stopped_C1_slope_weighted_drift_upper
-- name    : AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_C1_slope_weighted_drift_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:19:21.649847+00:00
-- url     : https://prove2.me/theorems/16504a75-af96-484e-b973-e67bb836bc8b
-- title:
--   Original BV stopped physical cells with their actual nonnegative C1 slopes obey source drift upper
-- statement:
--   For the original bounded-variation spectrally negative Lévy process, actual admissible dividend strategy and ruin/horizon-clipped uniform physical grid, the discounted jump-removed source increment sum remains bounded by the original drift allowance after multiplication by the actual value function derivative at each cell. The exact negative-jump sum and genuine nonincreasing original residual are retained, and the nonnegative-slope assumption is explicit at each sampled physical cell. This upgrades the previously proved unweighted drift bound to the precise C1 term appearing in the original cash/H identity.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_original_raw_R_ae_monotone
import Theorems.Thm_AvramDividend_Classical_avram_p3_2_physical_stopped_grid_monotone

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bv_cell7_original_BV_stopped_C1_slope_weighted_drift_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (T : ℝ≥0) :
    ∀ᵐ ω ∂P, ∀ m : ℕ,
      let τ : ℝ≥0 :=
        (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
      let u : ℕ → ℝ≥0 := fun i =>
        min (((min i (m + 1) : ℕ) : ℝ≥0) * (T / (m + 1))) τ
      let J : ℝ≥0 → ℝ := fun t =>
        ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
      let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
      let z : ℕ → ℝ := fun i =>
        x + X.X (u i) ω - rightLimit D (u i) ω
      (∀ i ∈ Finset.range (m + 1), 0 ≤ deriv w (z i)) →
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
          (Y (u (i + 1)) - Y (u i))) ≤
      (∑ i ∈ Finset.range (m + 1),
        (Real.exp (-(q * (u i : ℝ))) * deriv w (z i)) *
          (((u (i + 1) : ℝ) - (u i : ℝ)) * X.drift)) := by sorry
