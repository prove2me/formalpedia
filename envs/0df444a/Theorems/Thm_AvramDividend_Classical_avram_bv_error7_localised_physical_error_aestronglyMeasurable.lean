-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_error7_localised_physical_error_aestronglyMeasurable
-- name    : AvramDividend.Classical.avram_bv_error7_localised_physical_error_aestronglyMeasurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:36:09.093537+00:00
-- url     : https://prove2.me/theorems/ea9f6f58-c287-458f-b65a-19bd23d91dd3
-- title:
--   A.e. strongly measurable original physical errors remain a.e. strongly measurable when masked to a measurable localisation event
-- statement:
--   For the original physical-grid error sequence, a measurable localisation event and a.e. strongly measurable real residual ensure the masked residual is also a.e. strongly measurable, by the pinned Mathlib indicator lemma. This closes the otherwise separate measurability hypothesis used in the event-localised original BV positive-error expectation theorem. The result is pure measure theory and creates no new process, probability measure or stochastic hypothesis.
-- source:
--   Pinned Mathlib MeasureTheory.AEStronglyMeasurable.indicator at revision 0df444a360eaa60ab8c11dca51a86af692955474, with exact printed type checked in signature advise.

import Mathlib
open MeasureTheory Set Filter
open scoped Classical
noncomputable section

theorem AvramDividend.Classical.avram_bv_error7_localised_physical_error_aestronglyMeasurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω}
    (s : Set Ω) (hs : MeasurableSet s)
    (Err : ℕ → Ω → ℝ)
    (hErrMeas : ∀ m, AEStronglyMeasurable (Err m) P) :
    ∀ m, AEStronglyMeasurable
      (fun ω => if ω ∈ s then Err m ω else 0) P := by sorry
