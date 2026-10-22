-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
-- name    : AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:53:18.75419+00:00
-- url     : https://prove2.me/theorems/ea913fdd-443a-47bf-9e98-32cee265f873
-- title:
--   Exact actual capped-grid q-scale convergence at a fixed finite terminal horizon
-- statement:
--   For a spectrally negative Lévy path with continuous strict two-sided exit time τ distinct from a fixed finite horizon T, the actual bounded hittingBtwn grid clock gives a discounted stopped scale-function reward converging to the continuous value, whenever the terminal grid cap eventually reaches T and, when τ>T, stays before τ. Assumes W(0)=0. If τ<T, choose the positive margin T−τ, so no uniform one-unit buffer beyond the horizon is required.
-- source:
--   Generalized positive terminal-margin pathwise q-scale bridge, elementary NNReal subtraction identity and eventual cap conjunction. Publication v2 uses a declaration-only authoring scaffold and is scheduled after all imported parent theorems are authoritatively Proved.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_at_terminal_horizon
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
    (m : ℕ → ℕ)
    (hcapT : ∀ᶠ n in atTop, T ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : T < τ →
      ∀ᶠ n in atTop,
        (m n : ℝ≥0) * mesh n < τ)
    (K : ℕ → Ω → ℕ)
    (hK : ∀ n η, K n η = hittingBtwn
      (fun (j : ℕ) ξ => max
        (X.X ((j : ℝ≥0) * mesh n) ξ - upper)
        (lower - X.X ((j : ℝ≥0) * mesh n) ξ))
      (Set.Ioi (0 : ℝ)) 0 (m n) η) :
    Tendsto (fun n =>
      Real.exp (-(q * ((min ((K n ω : ℝ≥0) * mesh n) T) : ℝ))) *
        W (x + X.X (min ((K n ω : ℝ≥0) * mesh n) T) ω))
      atTop
      (𝓝 (Real.exp (-(q * ((min τ T) : ℝ))) *
        W (x + X.X (min τ T) ω))) := by
  sorry
