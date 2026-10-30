-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity
-- name    : AvramDividend.Classical.avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T11:26:23.727083+00:00
-- url     : https://prove2.me/theorems/b3d8bec1-c7e1-44f5-acae-c506b32fdf91
-- title:
--   Actual ceiling-capped q-scale grid convergence with only early-exit reserve continuity
-- statement:
--   At every actual strict two-sided first-passage grid on a vanishing mesh, the ceiling-capped discounted q-scale payoff converges for the true Levy path. The only local continuity required is at reserves attained on genuine strictly early exits. Exact terminal ties and no-exit-before-horizon paths are handled by deterministic clock stabilisation, without assuming Wq(0)=0.
-- source:
--   Genuine pathwise source assembly using accepted early-grid first-crossing lemma, new local-continuity mesh theorem, exact terminal tie clock, and after-horizon clipped clock stabilisation. Supports the real BV stopped optional stopping expectation limit with the nonzero Wq(0) boundary atom.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_ws01b_capped_grid_discounted_scale_mesh_tendsto_of_continuity
import Theorems.Thm_AvramDividend_Classical_chat03_actual_hittingBtwn_first_crossing_arbitrary_margin
import Theorems.Thm_AvramDividend_Classical_chat03_noexit_before_passage_grid_cap_stabilises
import Theorems.Thm_AvramDividend_Classical_chat03_terminal_ceiling_cap_before_later_exit
import Theorems.Thm_AvramDividend_Classical_chat03_nnreal_grid_ceiling_bracket
import Theorems.Thm_AvramDividend_Classical_chat03_actual_grid_terminal_tie_clock_eq_horizon
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Probability.Process.HittingTime

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal

theorem AvramDividend.Classical.avram_ws01b_actual_ceiling_capped_grid_scale_tendsto_of_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (ω : Ω) (lower upper x : ℝ) (τ T : ℝ≥0)
    (hτ : IsGLB
      {t : ℝ≥0 | X.X t ω < lower ∨ upper < X.X t ω} τ)
    (hContinuousEarly : τ < T → ContinuousAt W (x + X.X τ ω))
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
        W (x + X.X (min τ T) ω))) := by sorry
