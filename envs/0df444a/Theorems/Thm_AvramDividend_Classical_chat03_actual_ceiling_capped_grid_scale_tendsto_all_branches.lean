-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
-- name    : AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T05:07:29.10932+00:00
-- url     : https://prove2.me/theorems/178aba1f-8aea-4fdb-94d6-5dfb9f0091bd
-- title:
--   Ceiling-capped stopped scale grid reward converges at every finite exit, including terminal ties
-- statement:
--   For a finite strict two-sided continuous exit infimum and an actual bounded hittingBtwn uniform grid terminated by the ceiling index of horizon T, the discounted q-scale stopped reward converges to the continuous horizon-capped value, including a continuous exit precisely at T. This removes the off-horizon branch restriction by trichotomy and exact terminal-tie sampled-clock equality.
-- source:
--   Uses the already accepted off-horizon ceiling-capped scale theorem and the terminal-tie clock equality, with constant-sequence convergence in the equality case. Requires W(0)=0 and the pathwise IsGLB exit condition.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_ceiling_capped_grid_scale_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_actual_grid_terminal_tie_clock_eq_horizon
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_ceiling_capped_grid_scale_tendsto_all_branches
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
