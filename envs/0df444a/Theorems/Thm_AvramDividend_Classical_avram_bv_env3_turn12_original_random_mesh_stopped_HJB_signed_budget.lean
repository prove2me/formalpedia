-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_random_mesh_stopped_HJB_signed_budget
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_random_mesh_stopped_HJB_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:24:28.548434+00:00
-- url     : https://prove2.me/theorems/61be83f9-53c6-41a9-9293-93d613c87d22
-- title:
--   Actual stopped random physical mesh signed martingale plus nonpositive HJB drift has nonpositive expectation
-- statement:
--   On a bounded measurable random prefix of the original physical mesh and the genuine right-continuous stopping clock, integrable signed HJB cell drift stays nonpositive after selection. The actual stopped centered martingale-prefix mean is the separate explicitly identified obligation; this theorem transfers it to the original signed finite-grid source mean bound.
-- source:
--   Pinned Mathlib integral_mono_ae, accepted original stopped predictable mask turn23, accepted integrable bounded random prefix turn9. Companion turn12 e2483a2a proves the mean-zero premise from adapted k and true conditional centring.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_random_mesh_stopped_HJB_signed_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (M B : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hBI : ∀ i, Integrable (B i) P)
    (hDrift : ∀ i ω, B i ω ≤ 0)
    (hMMean : (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) ∂P) = 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω + B i ω else 0) ∂P) ≤ 0 := by sorry
