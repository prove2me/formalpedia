-- Prove2me | Theorems.Thm_AvramDividend_Classical_lintegral_stoppedEvent_horizon_tendsto
-- name    : AvramDividend.Classical.lintegral_stoppedEvent_horizon_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:06:58.553769+00:00
-- url     : https://prove2.me/theorems/e4300596-162d-4ff3-9de3-6c2abb006125
-- title:
--   Expected stopped-event rewards converge under increasing finite horizons
-- statement:
--   For an a priori finite real-valued stopping time and a uniformly bounded nonnegative reward, the expected reward on a stopped-history event restricted to τ≤n converges to the unrestricted stopped-event reward as the deterministic horizon n grows. Uses the Archimedean property and the bounded nonnegative integral dominated-convergence theorem.
-- source:
--   Root-connected localisation limit for extending the bounded stopped Lévy reward identity to arbitrary finite stopping times; prerequisite toward shifted-path strong Markov 61930a38-11f1-449e-bbb6-67d59c6d5ca8 and dividend up-exit splitting 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Algebra.Order.Archimedean.Defs

open MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.lintegral_stoppedEvent_horizon_tendsto
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (τ : Ω → ℝ≥0) (A : Set Ω)
    (f : Ω → ℝ≥0∞)
    (hMeas : ∀ n : ℕ,
      Measurable (Set.indicator
        (A ∩ {ω : Ω | τ ω ≤ (n : ℝ≥0)}) f))
    (C : ℝ≥0∞) (hBound : ∀ ω, f ω ≤ C)
    (hFinite : (∫⁻ _ : Ω, C ∂P) ≠ ∞) :
    Tendsto
      (fun n : ℕ => ∫⁻ ω, Set.indicator
        (A ∩ {ω' : Ω | τ ω' ≤ (n : ℝ≥0)}) f ω ∂P)
      atTop
      (nhds (∫⁻ ω, Set.indicator A f ω ∂P)) := by
  sorry
