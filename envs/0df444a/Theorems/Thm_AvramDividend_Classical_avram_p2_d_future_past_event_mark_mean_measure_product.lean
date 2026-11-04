-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_past_event_mark_mean_measure_product
-- name    : AvramDividend.Classical.avram_p2_d_future_past_event_mark_mean_measure_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:33:19.277194+00:00
-- url     : https://prove2.me/theorems/7f6aa554-e81f-4abb-93f9-832462eaeb29
-- title:
--   Original past-restricted jump mean factors as past mass times an exact mark measure
-- statement:
--   For the original Lévy process X, any deterministic window (s,t] and any event A measurable at time s, there is a genuine mark measure ρ such that the expected literal source jump count over A and marks B equals P(A)*ρ(B) for every Borel B. It holds with infinite counts and requires no ν-rate or auxiliary process.
-- source:
--   Combine Proved original future mark measure existence 03058d10-0af3-473b-8b84-d78f464c2f21 with Proved same-process past-event first-moment rectangle factorisation 264b3973-004f-414d-99ed-df5c2c01d29c. The theorem supplies P2-E a measure-valued predictable rectangle factorisation whose analytic identification ρ=(t-s)ν remains separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_d_future_past_event_mark_mean_measure_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    ∃ ρ : Measure ℝ, ∀ (B : Set ℝ), MeasurableSet B →
      (∫⁻ ω in A, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))) (Ioc s t ×ˢ B) ∂P) =
      P A * ρ B := by sorry
