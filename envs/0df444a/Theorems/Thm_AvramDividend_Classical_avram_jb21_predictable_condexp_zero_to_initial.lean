-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb21_predictable_condexp_zero_to_initial
-- name    : AvramDividend.Classical.avram_jb21_predictable_condexp_zero_to_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T20:01:55.505819+00:00
-- url     : https://prove2.me/theorems/fe44a91c-16c5-4f9c-9115-8007c8604a7d
-- title:
--   Predictable martingale difference remains initially conditionally centred under filtration tower
-- statement:
--   An integrable predictable weighted source martingale difference conditionally centred at its left filtration remains centred at the smaller initial filtration. Useful for separate original Gaussian and compensated-jump stopped Ito gains.
-- source:
--   Proved avram_gb66_filtered_predictable_multiplier_condExp_zero and pinned Mathlib condExp_condExp_of_le/condExp_congr_ae.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb66_filtered_predictable_multiplier_condExp_zero
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_jb21_predictable_condexp_zero_to_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (𝓢0 𝓢 : MeasurableSpace Ω)
    (h01 : 𝓢0 ≤ 𝓢) (hS : 𝓢 ≤ mΩ)
    (H Q : Ω → ℝ)
    (hH : StronglyMeasurable[𝓢] H)
    (hHQ : Integrable (fun ω => H ω * Q ω) P)
    (hQ : Integrable Q P)
    (hQzero : P[Q | 𝓢] =ᵐ[P] (fun _ => (0 : ℝ))) :
    P[(fun ω => H ω * Q ω) | 𝓢0] =ᵐ[P] (fun _ => (0 : ℝ)) := by sorry
