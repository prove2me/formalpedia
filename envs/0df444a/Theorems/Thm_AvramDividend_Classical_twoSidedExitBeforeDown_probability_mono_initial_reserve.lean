-- Prove2me | Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_initial_reserve
-- name    : AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:54:49.785065+00:00
-- url     : https://prove2.me/theorems/c8b9a3c4-2721-4fb5-841d-3d083acb4181
-- title:
--   Upper-first passage probability is increasing in the initial reserve
-- statement:
--   The increase in initial reserve decreases both canonical exit thresholds. Apply the Proved probability monotonicity lemma after proving the two real bounds.
-- source:
--   Monotonicity of strict upper exit before lower exit under reserve shifts.

import Theorems.Thm_AvramDividend_Classical_twoSidedExitBeforeDown_probability_mono_bounds
import Mathlib.Tactic.Linarith

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.twoSidedExitBeforeDown_probability_mono_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x y : ℝ) (hxy : x ≤ y) :
    P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ≤
    P {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} := by sorry
