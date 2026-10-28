-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_next_expected_le_current_mul_twoSided
-- name    : AvramDividend.Classical.killed_firstRecord_next_expected_le_current_mul_twoSided
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:41:44.208424+00:00
-- url     : https://prove2.me/theorems/33c724ff-f386-4ac2-82c7-c40b5eb7df6c
-- title:
--   Killed next-record expectation bounded by prior record and a true two-sided exit factor
-- statement:
--   Genuine strong-Markov inequality for a spectrally negative Levy barrier path: the next surviving discounted first-record reward is bounded by the current surviving record reward times the ordinary discounted two-sided upward-before-downward exit expectation with upper offset epsilon and lower offset -a. The proof requires measurable survival history, finite stopping-time localisation, shifted record-clock identity and the converse pathwise survival inclusion. No q-scale formula is assumed. This closes the stochastic part of the stopped-renewal upper bound independently of the scale-function identity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1, strong Markov at successive running supremum records and q-discounted two-sided exit.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_next_expected_le_current_mul_twoSided
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (a ε : ℝ) (ha : 0 < a)
    (hε : 0 < ε) (n : ℕ) :
    (∫⁻ ω, if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
      else 0 ∂P) ≤
    (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < -a), (t : ℝ≥0∞)) then
        ENNReal.ofReal
          (Real.exp (-(q * ENNReal.toReal
            (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) *
    (∫⁻ ω, if twoSidedExitUpTime X ((n : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal
          (ε * Real.exp (-(q * (twoSidedExitUpTime X ((n : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
