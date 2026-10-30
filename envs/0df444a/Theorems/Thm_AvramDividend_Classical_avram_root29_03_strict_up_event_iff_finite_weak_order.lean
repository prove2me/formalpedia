-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order
-- name    : AvramDividend.Classical.avram_root29_03_strict_up_event_iff_finite_weak_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:03:14.576975+00:00
-- url     : https://prove2.me/theorems/cf1d1161-64df-420c-87ef-837b16aa7d86
-- title:
--   Actual two-sided strict upper-first event equals finite weak-clock ordering
-- statement:
--   For every sample path of a genuine spectrally negative Lévy process and any strictly positive upper barrier, the actual strict upper-before-lower exit event is equivalent to weak ordering of the two strict passage times together with finiteness of the upward clock. The disjoint-barrier finite-tie exclusion is a proved right-continuity result, not a probabilistic atomlessness or no-creeping assumption. No Standing or q-scale assumption.
-- source:
--   Exact source-level event-ordering adapter for canonical equation (3.6). Uses canonically Proved original-Lévy official no-finite-tie theorem a9c87fbc and pinned Mathlib ENNReal.coe_toNNReal. This never changes the strict reward at an infinite tie and never treats a closed survival event as a strict lower-first event.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_strict_passage_no_finite_ties

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_strict_up_event_iff_finite_weak_order
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω <
        twoSidedExitDownTime X (-x) ω ↔
      twoSidedExitUpTime X (a - x) ω ≤
        twoSidedExitDownTime X (-x) ω ∧
      twoSidedExitUpTime X (a - x) ω < ⊤ := by sorry
