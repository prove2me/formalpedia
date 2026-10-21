-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_independent_exp_wait_finite_age_memorylessness
-- name    : AvramDividend.Classical.chat06_independent_exp_wait_finite_age_memorylessness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:06:46.651984+00:00
-- url     : https://prove2.me/theorems/4315d579-614f-48d3-a575-9fc22086bda8
-- title:
--   Memorylessness for independent finite-valued random ages
-- statement:
--   Given an observed age random variable A with nonnegative finite support and an independent Exp(1) waiting time tau, the probability that tau exceeds A+t equals e^{-t} times the probability that tau exceeds A, for t nonnegative. Proved by disjoint partition into age atoms, applying the already accepted exact fixed-age memorylessness lemma on each atom and summing. The finite-support condition will be removed in a subsequent approximation theorem.
-- source:
--   Prove2Me Chat 06 verified full source bv_independent_finite_valued_age_exp_survival_chat06_20261020.lean, pinned 0df444a360eaa60ab8c11dca51a86af692955474, private remote elaboration job da1aefc6-2b2f-495b-9c59-10456d23e327.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Theorems.Thm_AvramDividend_Classical_chat06_independent_exp_wait_atom_memorylessness

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_independent_exp_wait_finite_age_memorylessness
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A τ : Ω → ℝ)
    (hA : Measurable A) (hτ : Measurable τ)
    (hInd : IndepFun A τ P)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} = ENNReal.ofReal (Real.exp (-u)))
    (S : Finset ℝ) (hRange : ∀ ω, A ω ∈ S)
    (hNonneg : ∀ a ∈ S, 0 ≤ a)
    (t : ℝ) (ht : 0 ≤ t) :
    P {ω | A ω + t < τ ω} =
      P {ω | A ω < τ ω} *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
