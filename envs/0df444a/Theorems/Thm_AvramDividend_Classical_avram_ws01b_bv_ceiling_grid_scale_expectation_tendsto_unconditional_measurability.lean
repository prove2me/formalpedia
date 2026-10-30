-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_unconditional_measurability
-- name    : AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_unconditional_measurability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:59:16.791108+00:00
-- url     : https://prove2.me/theorems/bd4681c4-6315-4a58-a8d2-d13a4994fcd7
-- title:
--   Actual BV finite-horizon stopped-grid q-scale expectation convergence with automatic measurability
-- statement:
--   For the actual BV spectrally negative Lévy process and positive Laplace moment witness θ, the stopped first two-sided ceiling-grid discounted q-scale reward converges in expectation to the genuine finite-horizon continuous-stopped q-scale payoff, including no-exit paths and BV Wq(0)>0. The strong measurability of the continuous limit is automatically obtained from the canonically Proved original law mesh convergence and sampled reward measurability.
-- source:
--   Direct integration of accepted true-BV a.e limit measurability b9799867 and accepted genuine L² expectation convergence d29185dc; no extra hZ hypothesis.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_limit_aestrongly_measurable
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_of_measurable_limit

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01b_bv_ceiling_grid_scale_expectation_tendsto_unconditional_measurability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (θ : ℝ) (hθ : 0 ≤ θ) (hψ : q < X.ψ θ)
    (a x : ℝ) (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a)
    (T : ℝ≥0) (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0)) (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - (a-x))
        ((-x) - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η)
    :
    Integrable (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) P ∧
    Tendsto (fun n => ∫ ω,
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω) ∂P)
      atTop (𝓝 (∫ ω, (fun ω =>
      if min (twoSidedExitUpTime X (a-x) ω)
          (twoSidedExitDownTime X (-x) ω) < ⊤ then
        Real.exp (-(q * ((min
          (min (twoSidedExitUpTime X (a-x) ω)
            (twoSidedExitDownTime X (-x) ω)).toNNReal T) : ℝ))) *
          W (x + X.X (min
            (min (twoSidedExitUpTime X (a-x) ω)
              (twoSidedExitDownTime X (-x) ω)).toNNReal T) ω)
      else Real.exp (-(q * (T : ℝ))) * W (x + X.X T ω)) ω ∂P)) := by sorry
