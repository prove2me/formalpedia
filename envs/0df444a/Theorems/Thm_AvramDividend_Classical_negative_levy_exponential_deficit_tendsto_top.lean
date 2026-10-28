-- Prove2me | Theorems.Thm_AvramDividend_Classical_negative_levy_exponential_deficit_tendsto_top
-- name    : AvramDividend.Classical.negative_levy_exponential_deficit_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:55:13.717155+00:00
-- url     : https://prove2.me/theorems/e74ed6de-cd23-4525-95c6-25a6546914a3
-- title:
--   Divergence of the negative Lévy exponential compensation integral under infinite activity
-- statement:
--   If a measure is supported on strictly negative jump sizes and has infinite total mass there, the nonnegative Lévy exponential-deficit integral of 1−exp(ny) tends to infinity as n grows. For each y<0, the integrand increases to one. The monotone convergence theorem therefore yields the total infinite jump intensity as its limit. This is an analytic prerequisite for scale-function derivative blow-up at the origin.
-- source:
--   Lévy–Khintchine exponent and small-jump compensation; Kuznetsov, Kyprianou and Rivero, Theory of Scale Functions, Lemma 3.2; Avram, Palmowski and Pistorius (2007), Proposition 1, https://arxiv.org/pdf/math/0702893.

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FunProp

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

/-- The Lévy exponential deficit detects infinite negative-jump intensity. -/
theorem negative_levy_exponential_deficit_tendsto_top
    (ν : Measure ℝ)
    (hsupport : ν (Ici (0 : ℝ)) = 0)
    (hνinf : ν (Iio (0 : ℝ)) = ⊤) :
    Tendsto
      (fun n : ℕ => ∫⁻ y, ENNReal.ofReal
        (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop (nhds (⊤ : ℝ≥0∞)) := by sorry

end AvramDividend.Classical
