-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_actual_scale_expectation_of_continuous_martingale
-- name    : AvramDividend.Classical.chat03_capped_actual_scale_expectation_of_continuous_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:27:00.884812+00:00
-- url     : https://prove2.me/theorems/9b38c391-feb8-4020-a390-bedc56c26069
-- title:
--   Continuous martingale implies capped exit expectation without an initial-value assumption
-- statement:
--   Under an explicitly assumed continuous-time global discounted q-scale martingale and an adapted Lévy reserve, the true capped two-sided first-exit reward expectation equals W(x). Unlike the earlier bridge, the initial expected reward identity is derived automatically from X(0)=0 and the probability measure. The global martingale assumption is substantially stronger than the genuinely available downward-killed martingale and remains a conditional premise.
-- source:
--   Use the accepted chat03_discounted_scale_initial_expectation_eq to establish the initial condition, then apply the accepted chat03_capped_actual_scale_expectation_identity_from_continuous_martingale with all other hypotheses unchanged.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_capped_actual_scale_expectation_of_continuous_martingale
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
    (hAdapt : Adapted 𝓕 X.X)
    (hMart : Martingale
      (fun (t : ℝ≥0) ω => Real.exp (-(q * (t : ℝ))) *
        W (x + X.X t ω)) 𝓕 P) :
    (∫ ω, Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω) ∂P) = W x := by
  sorry
