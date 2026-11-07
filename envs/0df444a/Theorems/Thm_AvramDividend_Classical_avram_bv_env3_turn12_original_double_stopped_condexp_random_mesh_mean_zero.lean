-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn12_original_double_stopped_condexp_random_mesh_mean_zero
-- name    : AvramDividend.Classical.avram_bv_env3_turn12_original_double_stopped_condexp_random_mesh_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:19:52.660056+00:00
-- url     : https://prove2.me/theorems/e2483a2a-136d-4d66-ad75-dbe99ce80df6
-- title:
--   Original doubly stopped adapted random finite mesh centered increment is integrable and mean zero
-- statement:
--   With the original spectrally negative Levy probability measure, a genuine right-continuous stopping time and a bounded random mesh-prefix index predictable at each left endpoint, integrable physical source increments with conditional mean zero remain centered after both stopping and random mesh selection. The random sum itself is integrable. This removes one arbitrary grid-source centering assumption from the original BV signed finite-grid branch.
-- source:
--   Accepted original stopping-time selection d1eba19a, original predictable selection turn23, bounded source prefix turn9, Mathlib setIntegral_condExp.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn23_original_stopped_physical_grid_selection_predictable
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_integrable_bounded_measurable_source_prefix
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn9_original_centered_stopped_source_prefix_mean_zero
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_turn12_original_double_stopped_condexp_random_mesh_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (m : ℕ) (k : Ω → ℕ)
    (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hkAdapt : ∀ i,
      MeasurableSet[𝓕.rightCont (u i)] {ω : Ω | i < k ω})
    (M : ℕ → Ω → ℝ)
    (hMI : ∀ i, Integrable (M i) P)
    (hCondZero : ∀ i, ∀ᵐ ω ∂P,
      condExp (𝓕.rightCont (u i)) P (M i) ω = 0) :
    Integrable (fun ω => ∑ i ∈ Finset.range (k ω),
      if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      (if (u i : WithTop ℝ≥0) < τ ω then M i ω else 0) ∂P) = 0 := by sorry
