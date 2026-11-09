-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_jump12_initial_event_masked_stop
-- name    : AvramDividend.Classical.avram_ubv_jump12_initial_event_masked_stop
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T14:58:04.911472+00:00
-- url     : https://prove2.me/theorems/dd5bf1da-7839-42c2-9f76-697d690186b7
-- title:
--   An original right-continuous stopping clock remains stopping after masking by an initial event
-- statement:
--   For any stopping time of the original right-continuous filtration and any event measurable at time zero, the time equal to the original stopping time on the event and zero outside it is a stopping time of the same filtration. This is the source-faithful initial-event localisation needed for the compensated-jump mean budget.
-- source:
--   Required predictable initial-event clock restriction for source-exact Proved compact stopped Taylor compensation 744cf637 and the canonical positive-clock 0b1a879a route.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Nat BigOperators

theorem AvramDividend.Classical.avram_ubv_jump12_initial_event_masked_stop
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0)))
    (A : Set Ω) (hA : MeasurableSet[𝓕.rightCont 0] A) :
    IsStoppingTime 𝓕.rightCont
      (fun ω => ((A.indicator σ ω : ℝ≥0) : WithTop ℝ≥0)) := by sorry
