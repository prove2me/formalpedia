-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb21_original_initial_condexp_finite_predictable_gain
-- name    : AvramDividend.Classical.avram_jb21_original_initial_condexp_finite_predictable_gain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:05:51.695651+00:00
-- url     : https://prove2.me/theorems/0e39ef41-bd34-48f4-8f6d-42289b82684f
-- title:
--   Original finite predictable martingale gain is integrable and conditionally centred at initial information
-- statement:
--   For any finite family of predictable martingale differences on the original probability space, the sum is L1 and has zero conditional expectation at the smaller initial filtration. Applies to Gaussian and compensated-jump stopped Ito grids.
-- source:
--   Proved avram_gb66 filtered multiplier, Mathlib condExp_condExp_of_le, condExp_finset_sum and Filter.eventually_all_finset.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb66_filtered_predictable_multiplier_condExp_zero
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_jb21_original_initial_condexp_finite_predictable_gain
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ι : Type*}
    (S : Finset ι)
    (𝓢0 : MeasurableSpace Ω) (𝓢 : ι → MeasurableSpace Ω)
    (h01 : ∀ i ∈ S, 𝓢0 ≤ 𝓢 i)
    (hS : ∀ i ∈ S, 𝓢 i ≤ mΩ)
    (H Q : ι → Ω → ℝ)
    (hH : ∀ i ∈ S, StronglyMeasurable[𝓢 i] (H i))
    (hQ : ∀ i ∈ S, Integrable (Q i) P)
    (hHQ : ∀ i ∈ S,
      Integrable (fun ω => H i ω * Q i ω) P)
    (hQzero : ∀ i ∈ S,
      P[Q i | 𝓢 i] =ᵐ[P] (fun _ => (0 : ℝ))) :
    Integrable (fun ω => ∑ i ∈ S, H i ω * Q i ω) P ∧
    P[(fun ω => ∑ i ∈ S, H i ω * Q i ω) | 𝓢0]
      =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
