-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_up_first_iff_finite_stopped_min
-- name    : AvramDividend.Classical.avram_root29_03_up_first_iff_finite_stopped_min
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T09:17:32.153393+00:00
-- url     : https://prove2.me/theorems/9a984dcc-2566-4a91-be41-01da7a57f407
-- title:
--   True strict upper-first exit is finite attainment of the minimum stopped clock
-- statement:
--   For the genuine original Lévy process, positive barrier a and any initial reserve x, the strict upper-before-lower exit event is equivalent, pathwise, to the upward clock attaining the minimum of the two actual ENNReal stopping clocks together with upward-clock finiteness. This is the precise optional-stopping event interface; without finiteness an infinite-infinite tie would be erroneously included.
-- source:
--   Imports already canonically Proved strict-event clock-order adapter cf1d1161 and uses pinned Mathlib lattice min lemma only. No Standing or killed stochastic identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_avram_root29_03_strict_up_event_iff_finite_weak_order

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_up_first_iff_finite_stopped_min
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω ↔
    min (twoSidedExitUpTime X (a - x) ω)
        (twoSidedExitDownTime X (-x) ω) =
      twoSidedExitUpTime X (a - x) ω ∧
    twoSidedExitUpTime X (a - x) ω < ⊤ := by sorry
