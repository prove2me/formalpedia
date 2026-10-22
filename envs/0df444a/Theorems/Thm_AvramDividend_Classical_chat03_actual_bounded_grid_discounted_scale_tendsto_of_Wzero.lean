-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
-- name    : AvramDividend.Classical.chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:31:36.037712+00:00
-- url     : https://prove2.me/theorems/4e84e6dc-5510-4758-9456-e716ae47df69
-- title:
--   Actual bounded first-grid discounted q-scale reward converges when W vanishes at zero
-- statement:
--   For an actual Mathlib bounded first strict two-sided grid hitting clock K of a spectrally negative Lévy process, on a fixed sample path with finite continuous first strict passage infimum, a vanishing positive mesh and sufficiently distant terminal cap, the exact discounted q-scale reward evaluated at the capped K clock converges to the continuous capped first-passage reward provided W(0)=0. This closes the pathwise convergence hypothesis needed by the accepted grid stopped-scale expectation convergence theorem in the zero-origin regime.
-- source:
--   Compose independently Proved actual bounded hittingBtwn eventual first-crossing identification with Proved exponential-discounted capped q-scale mesh convergence.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_eventually_first_strict_grid_crossing
import Theorems.Thm_AvramDividend_Classical_chat03_exponential_discount_first_grid_scale_tendsto
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcap : ∀ᶠ n in atTop, τ + 1 ≤ (m n : ℝ≥0) * mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by sorry
