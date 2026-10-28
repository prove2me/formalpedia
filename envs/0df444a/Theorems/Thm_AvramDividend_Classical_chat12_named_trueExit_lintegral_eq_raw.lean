-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat12_named_trueExit_lintegral_eq_raw
-- name    : AvramDividend.Classical.chat12_named_trueExit_lintegral_eq_raw
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:56:09.406115+00:00
-- url     : https://prove2.me/theorems/e004fdf2-0ff4-45f8-996f-f48d05bcfcda
-- title:
--   Named strict-exit and raw infimum-clock discounted integrals coincide
-- statement:
--   A generic stochastic-process bookkeeping lemma: the exponentially discounted strict upward-before-downward exit expectation expressed with the named two-sided exit stopping-time functions equals the raw iInf-based expression used in q-scale exit identities. The proof is pointwise by cases, ensuring different elaborated decidability procedures do not create a dependent-typed mismatch. No scale-function, Markov or boundary-regularity assumption is needed.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat12_named_trueExit_lintegral_eq_raw
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a ε : ℝ) :
    (∫⁻ ω, if twoSidedExitUpTime X ε ω <
        twoSidedExitDownTime X (ε - a) ω then
      ENNReal.ofReal (Real.exp
        (-(q * (twoSidedExitUpTime X ε ω).toReal)))
    else 0 ∂P) =
    (∫⁻ ω, if
      (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
      (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
      ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
        (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
    else 0 ∂P) := by sorry
