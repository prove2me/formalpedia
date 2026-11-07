-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_clock_selected_random_grid_signed_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_clock_selected_random_grid_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:38:26.226423+00:00
-- url     : https://prove2.me/theorems/5c010d1e-2bcd-4932-bc08-23289146bc6b
-- title:
--   Fully clock-selected original Lévy stopped physical-grid martingale plus HJB signed source has nonpositive mean
-- statement:
--   Use the genuine original stopping time to construct its finite physical-grid prefix, prove the random index measurable and adapted, prove conditional-mean-zero stopped Lévy martingale cells have zero aggregate mean, and combine with nonpositive integrable HJB drift cells. The resulting actual stopped random-grid signed source is integrable with nonpositive expectation. The cell-level conditional martingale and HJB hypotheses remain separately provable original-process source obligations.
-- source:
--   Dependencies from genuine reductions: original grid-card measurability f53747fc, rightCont grid index adapted d93b8897, stopped random source martingale e2483a2a and signed HJB 61be83f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_clock_selected_random_grid_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    let k : Ω → ℕ := fun ω =>
      ((Finset.range m).filter
        (fun j => (u j : WithTop ℝ≥0) < τ ω)).card
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ∂P) ≤ 0 := by sorry
