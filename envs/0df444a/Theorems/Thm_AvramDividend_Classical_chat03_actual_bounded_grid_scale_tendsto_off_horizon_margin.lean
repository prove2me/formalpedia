-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
-- name    : AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:41:45.690434+00:00
-- url     : https://prove2.me/theorems/4bfba8b2-ce47-4075-ab37-51b48fef409e
-- title:
--   Exact capped hitting-clock q-scale convergence for any positive early-exit margin
-- statement:
--   For a Lévy path with finite continuous strict two-sided exit infimum τ different from finite horizon T, a genuinely bounded hittingBtwn sampled clock converges in discounted q-scale reward to the continuous horizon-capped value, assuming W(0)=0. In the early-exit case τ<T, the terminal-grid coverage margin may be any ε>0, permitting terminal time exactly T when ε<T−τ. In the no-exit case T<τ, terminal samples eventually remain between T and τ. This extends the earlier one-unit-margin result.
-- source:
--   Generalized actual hittingBtwn earliest crossing at arbitrary margin, Proved exponential discounted first-grid scale convergence and Proved no-exit bounded-grid clock stabilisation. Publication v2 uses a declaration-only authoring scaffold and is scheduled after all imported parent theorems are authoritatively Proved.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
import Theorems.Thm_AvramDividend_Classical_chat03_exponential_discount_first_grid_scale_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Mathlib.Probability.Process.HittingTime
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Set Filter Topology
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_actual_bounded_grid_scale_tendsto_off_horizon_margin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (ε : ℝ≥0) (hε : 0 < ε)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hbranch : τ < T ∨ T < τ)
    (mesh : ℕ → ℝ≥0)
    (hmesh : Tendsto mesh atTop (𝓝 0))
    (hpos : ∀ n, 0 < mesh n)
    (m : ℕ → ℕ)
    (hcapBefore : τ < T →
      ∀ᶠ n in atTop, τ + ε ≤ (m n : ℝ≥0) * mesh n)
    (hcapAfter : T < τ →
      ∀ᶠ n in atTop,
        T ≤ (m n : ℝ≥0) * mesh n ∧
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
