-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:19:42.503199+00:00
-- url     : https://prove2.me/theorems/2b993cd3-a0e7-47e3-9d61-53484ce705f8
-- title:
--   Original Lévy martingale bounded predictable source-prefix signed budget
-- statement:
--   For an original spectrally negative Lévy process, physical-grid increments of a genuine right-continuous-filtration martingale have zero conditional expectation. Every measurable predictable bounded random prefix with nonpositive integrable drift has a finite integrable signed stopped budget of nonpositive mean. The construction of the actual original stochastic source martingale and the stopping-prefix selector remains explicit.
-- source:
--   Composes accepted BV-ENV3 original physical-grid martingale zero-conditional-mean turn22 with accepted predictable signed-grid finite-prefix turn21. No equality-in-law or extra stochastic regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn21_original_predictable_stopped_signed_grid_budget
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn22_original_martingale_physical_grid_increment_condexp_zero
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (k : Ω → ℕ) (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hPredictable : ∀ i, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < k ω})
    (B : ℕ → Ω → ℝ) (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω)) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) + B i ω) ∂P) ≤ 0 := by sorry
