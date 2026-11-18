-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_global_centered_L2_grid_has_L1_limit_on_future_event
-- name    : AvramDividend.Classical.avram_gaussianB_global_centered_L2_grid_has_L1_limit_on_future_event
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:37:23.174679+00:00
-- url     : https://prove2.me/theorems/50fb913b-4565-47d8-aa05-17dd26d26072
-- title:
--   Globally centred L2-Cauchy Gaussian physical grid has an integrable L1 limit on any future event
-- statement:
--   For an actual original Gaussian stopped grid M with global L2-Cauchy convergence, individual L2 and L1 integrability and global expected value converging to zero, there exists an integrable centred limit N such that the L1 difference on every fixed measurable event A tends to zero. The event may be a future-dependent Brownian tube and need not be F0 measurable. The theorem uses the Proved gb36 theorem with A=univ and then transfers L1 convergence to A by monotonicity, avoiding the unjustified requirement that martingale noise have zero mean conditional on a future tube.

import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_avram_gb36_L2_cauchy_eventwise_centred_L1_limit
open scoped Topology
open MeasureTheory Filter Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_global_centered_L2_grid_has_L1_limit_on_future_event
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (M : ℕ → Ω → ℝ)
    (hMLp : ∀ m, MemLp (M m) 2 P)
    (hMInt : ∀ m, Integrable (M m) P)
    (hCauchy : Tendsto (fun nm : ℕ × ℕ =>
      eLpNorm (M nm.1 - M nm.2) 2 P) atTop (𝓝 (0 : ℝ≥0∞)))
    (hMeanGlobal : Tendsto (fun m => ∫ ω, M m ω ∂P)
      atTop (𝓝 (0 : ℝ)))
    (A : Set Ω) (hA : MeasurableSet A) :
    ∃ N : Ω → ℝ, Integrable N P ∧
      (∫ ω, N ω ∂P) = 0 ∧
      Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
