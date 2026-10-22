-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_unrestricted_independent_exp_random_age_memorylessness
-- name    : AvramDividend.Classical.chat06_unrestricted_independent_exp_random_age_memorylessness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T06:35:24.45745+00:00
-- url     : https://prove2.me/theorems/e0e40e1f-5c54-4852-add7-aeffecb42027
-- title:
--   Exact exponential memorylessness for unrestricted nonnegative random ages
-- statement:
--   For any nonnegative measurable random age A, not necessarily finite-valued or discrete, independent of an Exp(1) waiting time tau, its residual survival probability factorises exactly with exp(-t) for all t>=0. The proof uses the complete joint product law, the exact Tonelli representation of random threshold survival and pointwise exponential-kernel scaling over the marginal age law.
-- source:
--   Chat 06 73-line candidate based on independently pinned remotely elaborated helper propositions; theorem depends on accepted proofs of the two imported Tonelli and scaling helper targets before official publication or proof submission.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_independent_random_age_survival_lintegral
import Theorems.Thm_AvramDividend_Classical_chat06_exponential_random_age_lintegral_scaling

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_unrestricted_independent_exp_random_age_memorylessness
    {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (A τ : Ω → ℝ)
    (hA : Measurable A) (hτ : Measurable τ)
    (hInd : IndepFun A τ P)
    (hNonneg : ∀ᵐ ω ∂P, 0 ≤ A ω)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | A ω + t < τ ω} =
      P {ω | A ω < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
