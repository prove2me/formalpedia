-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:55:38.041216+00:00
-- url     : https://prove2.me/theorems/67302ed2-b2f4-4b2c-8ee1-8970ef4db7d3
-- title:
--   Original clock-stopped finite-grid martingale and negative HJB drift expectation
-- statement:
--   For a genuine original right-continuous-filtration stopping time tau and physical-grid times u_i, the sum over i<m of source martingale differences M_i and nonpositive HJB drift pieces B_i masked by the event u_i<tau is integrable and has nonpositive expectation. Each source increment has integrable zero original conditional mean at u_i, with no independent random-index assumptions.
-- source:
--   Pinned Mathlib IsStoppingTime, setIntegral_condExp, integral_indicator, integrable_finset_sum and integral_finset_sum. Original SpectrallyNegativeLevy.isProbability. The actual original stopped C1 chain identifies increments externally; no equality-in-law or stochastic regularity invented.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn24_original_stopping_clock_signed_finite_grid_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0)
      ∂P) ≤ 0 := by sorry
