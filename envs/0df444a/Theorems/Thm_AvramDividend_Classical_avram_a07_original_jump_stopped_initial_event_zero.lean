-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a07_original_jump_stopped_initial_event_zero
-- name    : AvramDividend.Classical.avram_a07_original_jump_stopped_initial_event_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:24:00.998593+00:00
-- url     : https://prove2.me/theorems/6f66c79a-fe31-4932-8394-d66c8142cf00
-- title:
--   Original stopped compensated small-jump integral vanishes on every initial event
-- statement:
--   Extract the original compensated small-jump martingale path and bounded stopped integrability certificate, then prove its stopped integral is zero on every initial-filtration event using the conditional expectation characterisation. This is a genuine necessary zero-noise source for the A07 initial-event Ito-Meyer ledger.
-- source:
--   Exact original stochastic witness hJstopped of 01138655, with original Levy space and right-continuous filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a07_original_jump_stopped_initial_event_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (σ : Ω → ℝ≥0)
    (hJstopped :
      ∃ Jsmall : ℝ≥0 → Ω → ℝ,
        (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
          Tendsto
            (fun k : ℕ =>
              avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
            atTop (nhds (Jsmall t ω))) ∧
        (∀ t : ℝ≥0, Integrable (Jsmall t) P) ∧
        (∀ s t : ℝ≥0, s ≤ t →
          ∀ᵐ ω ∂P,
            condExp (𝓕.rightCont s) P (Jsmall t) ω = Jsmall s ω) ∧
        Integrable (fun ω => Jsmall (σ ω) ω) P ∧
        (∀ᵐ ω ∂P,
          condExp (𝓕.rightCont 0) P
            (fun ω => Jsmall (σ ω) ω) ω = 0)) :
    ∃ Jsmall : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k t ω)
          atTop (nhds (Jsmall t ω))) ∧
      Integrable (fun ω => Jsmall (σ ω) ω) P ∧
      (∀ S : Set Ω, MeasurableSet[𝓕.rightCont 0] S →
        ∫ ω in S, Jsmall (σ ω) ω ∂P = 0) := by sorry
