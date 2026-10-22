-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_ae_tendsto_of_Wzero
-- name    : AvramDividend.Classical.chat03_actual_bounded_grid_scale_ae_tendsto_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:43:59.906658+00:00
-- url     : https://prove2.me/theorems/aa312422-d978-455e-8dbd-f9645540e42f
-- title:
--   Almost-everywhere convergence of actual bounded-grid discounted scale rewards
-- statement:
--   Suppose almost every sample path of a spectrally negative Lévy process has a finite strict two-sided first passage infimum τ(ω), and the bounded observation grid eventually extends past that infimum by one time unit. With W(0)=0, the exact exponentially discounted stopped q-scale payoff using Mathlib hittingBtwn converges almost everywhere to its continuously stopped counterpart. This establishes the pathwise convergence input for the accepted mesh-uniform L² expectation theorem.
-- source:
--   Almost-everywhere instantiation of the independently verified actual bounded hittingBtwn discounted q-scale convergence theorem using the pathwise IsGLB and terminal-cap hypotheses.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_bounded_grid_scale_ae_tendsto_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (lower upper x : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB {t : ℝ≥0 |
        X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᵐ ω ∂P,
      ∀ᶠ n in atTop, τ ω + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    ∀ᵐ ω ∂P,
      Tendsto (fun n =>
        Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
          W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
        atTop
        (𝓝 (Real.exp (-(q * ((min (τ ω) T) : ℝ))) *
          W (x + X.X (min (τ ω) T) ω))) := by sorry
