-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_nonint_tight_deficit_meas_of_sources
-- name    : AvramDividend.Classical.avram_a19_nonint_tight_deficit_meas_of_sources
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T17:28:52.393288+00:00
-- url     : https://prove2.me/theorems/6b442d55-63a3-4770-aefd-2e52c77ef727
-- title:
--   A.e. measurable original signed-source tight positive deficit from measurable physical components
-- statement:
--   A.e. strong measurability of the true original payoff, correction and signed drift suffices to measure their positive tight deficit without signed L1 assumptions.
-- source:
--   Independent generic real-valued measurability adapter for original Avram A19 physical signed-source certificate b645342a, using real Borel sum/sub/max closure.

import Mathlib
open Classical MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_nonint_tight_deficit_meas_of_sources
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (F M B : ℕ → Ω → ℝ) (c : ℝ)
    (hF : ∀ n, AEStronglyMeasurable (F n) P)
    (hM : ∀ n, AEStronglyMeasurable (M n) P)
    (hB : ∀ n, AEStronglyMeasurable (B n) P) :
    ∀ n, AEStronglyMeasurable
      (fun ω => max (F n ω - (c + (M n ω + B n ω))) 0) P := by sorry
