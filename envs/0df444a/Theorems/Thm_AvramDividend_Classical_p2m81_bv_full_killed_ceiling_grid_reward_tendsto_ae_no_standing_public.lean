-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_full_killed_ceiling_grid_reward_tendsto_ae_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_full_killed_ceiling_grid_reward_tendsto_ae_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:46:10.824461+00:00
-- url     : https://prove2.me/theorems/05ef7242-313e-471d-b871-88bc3b864b1c
-- title:
--   Standing-free full killed ceiling grid reward convergence
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, the history-killed ceiling grid reward converges almost surely on every path to the corresponding lower-first, surviving-horizon, or upper-first payoff.
-- source:
--   Adapted from exact accepted source of avram_ws01b_bv_full_killed_ceiling_grid_reward_tendsto_ae by replacing all three Standing window-convergence imports with positive-root no-Standing counterparts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_full_killed_ceiling_grid_reward_tendsto_ae_no_standing_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ : ℝ) (hq : 0 < q) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (W : ℝ → ℝ)
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
