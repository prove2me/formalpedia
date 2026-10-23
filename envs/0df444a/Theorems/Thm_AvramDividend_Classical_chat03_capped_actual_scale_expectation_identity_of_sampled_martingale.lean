-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_actual_scale_expectation_identity_of_sampled_martingale
-- name    : AvramDividend.Classical.chat03_capped_actual_scale_expectation_identity_of_sampled_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T07:19:29.912398+00:00
-- url     : https://prove2.me/theorems/cdbbfa9c-3f9f-4dd7-9d35-ce3642dd56b1
-- title:
--   Sampled martingale optional stopping implies capped continuous q-scale identity
-- statement:
--   If the sampled discounted q-scale rewards are genuine martingales for each finite clipped grid, and their initial expectations equal W(x), bounded two-sided grid optional sampling identifies each actual first-exit reward expectation with W(x). The accepted full finite-horizon convergence result then gives the continuous stopped q-scale expectation identity, including first exits occurring exactly at the terminal horizon. The martingale condition remains an explicit separate stochastic hypothesis.
-- source:
--   Combine accepted bounded first-crossing martingale identity, exact clipped hitting-index congruence, and accepted actual ceiling-capped stopped expectation convergence. Apply uniqueness of real limits.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_expectation_tendsto_full
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_clipped_hitting_congr
import Theorems.Thm_AvramDividend_Classical_chat03_two_sided_grid_stopped_martingale_identity
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_capped_actual_scale_expectation_identity_of_sampled_martingale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (θ x : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (lower upper : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P, IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0) (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    (clock : ℕ → ℕ → ℝ≥0)
    (hclock : ∀ n k, clock n k = min ((k : ℝ≥0) * mesh n) T)
    (H : ℕ → Filtration ℕ mΩ)
    (hAdapt : ∀ n, Adapted (H n) (fun k ω => X.X (clock n k) ω))
    (hMart : ∀ n, Martingale
      (fun k ω => Real.exp (-(q * (clock n k : ℝ))) *
        W (x + X.X (clock n k) ω)) (H n) P)
    (hInit : ∀ n, (∫ ω,
      Real.exp (-(q * (clock n 0 : ℝ))) *
        W (x + X.X (clock n 0) ω) ∂P) = W x) :
    (∫ ω, Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω) ∂P) = W x := by
  sorry
