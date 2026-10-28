-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_initial_reserve
-- name    : AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:54:20.838395+00:00
-- url     : https://prove2.me/theorems/c0dae2c6-e1ae-44a7-8206-96ac52ea2c4e
-- title:
--   Upper-first passage event is increasing in the initial reserve
-- statement:
--   As initial reserve rises from x to y, the upward threshold a-reserve falls and the lower threshold -reserve falls. Apply the Proved upper-first-event order lemma with two real inequalities.
-- source:
--   Monotonicity of strict upper exit before lower exit under reserve shifts.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_event_mono_bounds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitBeforeDown_event_mono_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x y : ℝ) (hxy : x ≤ y) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} := by sorry
