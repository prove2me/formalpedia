-- Prove2me | Theorems.Thm_AvramDividend_Classical_p2m81_bv_finite_exit_ceiling_grid_scale_tendsto_ae_no_standing_public
-- name    : AvramDividend.Classical.p2m81_bv_finite_exit_ceiling_grid_scale_tendsto_ae_no_standing_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T00:45:51.587055+00:00
-- url     : https://prove2.me/theorems/1314d2ef-d3ad-4248-8876-1af465311bc1
-- title:
--   Standing-free finite-exit BV ceiling grid q-scale convergence
-- statement:
--   For a bounded-variation spectrally negative Levy process with a positive q-root, the ceiling-capped first-grid discounted q-scale payoff converges almost surely on finite two-sided-exit trajectories.
-- source:
--   Adapted from exact accepted source of avram_ws01b_bv_finite_exit_ceiling_grid_scale_tendsto_ae by replacing the Standing scale-continuity import with its positive-root no-Standing counterpart.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.p2m81_bv_finite_exit_ceiling_grid_scale_tendsto_ae_no_standing_public
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
      min (twoSidedExitUpTime X (a-x) ω)
        (twoSidedExitDownTime X (-x) ω) < ⊤ →
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω))) := by sorry
