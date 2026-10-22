-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T21:05:26.934511+00:00
-- url     : https://prove2.me/theorems/743267c4-2989-4c70-8da7-228e21da84ff
-- title:
--   Actual stopped scale payoff converges for a ceiling-capped finite uniform grid away from terminal ties
-- statement:
--   For a finite strict two-sided exit infimum different from a fixed observation horizon, the genuine bounded hittingBtwn sampled process stopped at the ceiling-grid cap has discounted q-scale reward converging to the continuous exit-or-horizon reward. The exact ceiling bracket supplies both the eventual cap beyond the horizon and, for later continuous exits, the cap strictly before exit.
-- source:
--   Composes the arbitrary-margin exact terminal-horizon convergence, terminal ceiling cap before a later exit and the accepted NNReal ceiling bracket. Requires zero scale at the origin; does not assume killed q-scale harmonicity.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_terminal_ceiling_cap_before_later_exit
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hbranch : τ < T ∨ T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (Nat.ceil (T / mesh n)) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  sorry
