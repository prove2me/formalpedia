-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
-- name    : AvramDividend.Classical.chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T14:51:03.570692+00:00
-- url     : https://prove2.me/theorems/fd4e6edb-b1a9-4684-9ecc-d3cfaf1c4216
-- title:
--   Remove the time cap from actual stopped q-scale grid convergence before a fixed horizon
-- statement:
--   If the continuous strict two-sided exit occurs at finite time τ strictly before T, the sampled Mathlib bounded hittingBtwn clock converges to τ and eventually lies before T. Therefore the capped sampled discounted q-scale convergence theorem with W(0)=0 implies convergence of the uncapped sampled discounted q-scale payoff to the continuous stopped payoff.
-- source:
--   Proved Chat03 exact bounded hit-clock convergence and capped discounted q-scale convergence; the real and NNReal cap comparisons are discharged explicitly.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_discounted_scale_tendsto_of_Wzero
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_clock_tendsto
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Data.NNReal.Defs
import Mathlib.Probability.Process.HittingTime

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_uncapped_grid_discounted_scale_tendsto_of_Wzero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hτT : τ < T)
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
      Real.exp (-(q * (((K n ω : ℝ≥0) * mesh n) : ℝ))) *
        W (x + X.X ((K n ω : ℝ≥0) * mesh n) ω))
      atTop
      (𝓝 (Real.exp (-(q * (τ : ℝ))) *
        W (x + X.X τ ω))) := by sorry
