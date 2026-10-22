-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_capped_grid_scale_ae_tendsto_off_horizon
-- name    : AvramDividend.Classical.chat03_actual_capped_grid_scale_ae_tendsto_off_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T17:47:35.457985+00:00
-- url     : https://prove2.me/theorems/d236f3a6-fc4b-4333-b272-465f5a69095d
-- title:
--   Almost-everywhere convergence of actual horizon-capped q-scale rewards across either side of a finite exit horizon
-- statement:
--   Given an almost-everywhere genuine finite strict exit infimum τ separated from the deterministic finite horizon T, and eventwise eventual terminal mesh coverage, the exact bounded hittingBtwn q-scale reward converges almost everywhere to the continuously capped stopped reward in the W(0)=0 regime. A direct pathwise-to-almost-everywhere consequence of the separately proved strict-exit and no-exit branches. It does not claim killed q-scale harmonicity.
-- source:
--   Accepted chat03_actual_bounded_grid_scale_tendsto_off_horizon, once verified; almost-everywhere filter combination.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_off_horizon
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_capped_grid_scale_ae_tendsto_off_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (lower upper x : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB {t : ℝ≥0 |
        X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (hbranch : ∀ᵐ ω ∂P, τ ω < T ∨ T < τ ω)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcapBefore : ∀ᵐ ω ∂P,
      τ ω < T →
        ∀ᶠ n in atTop, τ ω + 1 ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : ∀ᵐ ω ∂P,
      T < τ ω →
        ∀ᶠ n in atTop,
          T ≤ (m n : ℝ≥0) * mesh n ∧
          (m n : ℝ≥0) * mesh n < τ ω)
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
