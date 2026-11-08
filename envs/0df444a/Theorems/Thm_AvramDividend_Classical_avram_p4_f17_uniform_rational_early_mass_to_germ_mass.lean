-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f17_uniform_rational_early_mass_to_germ_mass
-- name    : AvramDividend.Classical.avram_p4_f17_uniform_rational_early_mass_to_germ_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:18:20.414747+00:00
-- url     : https://prove2.me/theorems/1b53e352-c84b-42c0-972b-b6520349b733
-- title:
--   Uniform positive rational-horizon excursion mass survives to the time-zero germ
-- statement:
--   For a finite measure and a process whose values at rational nonnegative times are measurable, suppose there is a strictly positive common lower bound for the probability of some positive rational-time observation before each positive horizon. Continuity from above on a countable reciprocal horizon sequence gives positive probability of positive rational observations arbitrarily close to time zero. This isolates the probability-continuity step needed after the quantitative first-passage transform; a separate right-continuity lemma transfers the rational germ event to the original process's real-time germ.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f17_uniform_rational_early_mass_to_germ_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (B : ℝ≥0 → Ω → ℝ)
    (hB : ∀ q : ℚ≥0, Measurable (B (q : ℝ≥0)))
    (a : ℝ≥0∞) (ha : 0 < a)
    (hUniform : ∀ ε : ℝ≥0, 0 < ε →
      a ≤ P {ω : Ω | ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω}) :
    0 < P.real {ω : Ω | ∀ ε : ℝ≥0, 0 < ε →
      ∃ q : ℚ≥0, (q : ℝ≥0) < ε ∧ 0 < B (q : ℝ≥0) ω} := by sorry
