-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_terminal_grid_scale_ae_tendsto
-- name    : AvramDividend.Classical.chat03_actual_terminal_grid_scale_ae_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:04:24.071331+00:00
-- url     : https://prove2.me/theorems/ebaa73c9-34c9-42b4-979b-714fcb2bd74e
-- title:
--   Almost-everywhere convergence of actual bounded stopped q-scale grid values at terminal horizon
-- statement:
--   For a measurable spectrally negative Lévy process and scale function W with W(0)=0, suppose almost every path has a finite continuous strict two-sided exit infimum τ distinct from terminal time T, grid caps eventually reach T, and on no-exit paths their caps remain below τ. Then actual bounded hittingBtwn grid discounted scale rewards capped at T converge pointwise almost everywhere to the continuous horizon-capped reward.
-- source:
--   Exact pathwise fixed-horizon q-scale convergence and an almost-everywhere lifting using filter_upwards. Publication v2 uses a declaration-only authoring scaffold and is scheduled after all imported parent theorems are authoritatively Proved.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_terminal_grid_scale_ae_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (lower upper x : ℝ) (T : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτ : ∀ᵐ ω ∂P,
      IsGLB
        {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} (τ ω))
    (hbranch : ∀ᵐ ω ∂P, τ ω < T ∨ T < τ ω)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcapT : ∀ᶠ n in atTop, T ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : ∀ᵐ ω ∂P,
      T < τ ω →
        ∀ᶠ n in atTop, (m n : ℝ≥0) * mesh n < τ ω)
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
          W (x + X.X (min (τ ω) T) ω))) := by
  sorry
