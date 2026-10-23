-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_capped_actual_scale_expectation_identity_from_continuous_martingale
-- name    : AvramDividend.Classical.chat03_capped_actual_scale_expectation_identity_from_continuous_martingale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T08:19:05.544823+00:00
-- url     : https://prove2.me/theorems/a4b18bbd-04f8-474c-a148-08c286674c50
-- title:
--   Finite-horizon scale identity conditional on a global continuous-time q-scale martingale
-- statement:
--   Conditional bridge: any adapted Lévy reserve whose globally discounted q-scale reward is a continuous-time martingale has the expected finite-horizon stopped reward identity at the actual two-sided exit. The unstopped martingale assumption is generally stronger than killed q-scale harmonicity and remains explicit; further downward-killed martingale work is required for the original theorem.
-- source:
--   The declaration imports only definitions and Mathlib needed for its statement; the separate Lean proof additionally imports the already Proved sampled-martingale exit bridge, thereby reducing unnecessary remote authoring import closure.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Probability.Process.HittingTime
import Mathlib.Probability.Martingale.Basic

open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.chat03_capped_actual_scale_expectation_identity_from_continuous_martingale
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
        W (x + X.X t ω)) 𝓕 P)
    (hInit : ∀ n, (∫ ω,
      Real.exp (-(q * (clock n 0 : ℝ))) *
        W (x + X.X (clock n 0) ω) ∂P) = W x) :
    (∫ ω, Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
      W (x + X.X (min (τ ω) T) ω) ∂P) = W x := by
  sorry
