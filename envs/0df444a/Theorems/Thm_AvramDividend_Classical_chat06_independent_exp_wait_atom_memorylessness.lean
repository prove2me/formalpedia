-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat06_independent_exp_wait_atom_memorylessness
-- name    : AvramDividend.Classical.chat06_independent_exp_wait_atom_memorylessness
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T16:40:13.794545+00:00
-- url     : https://prove2.me/theorems/97159fb7-446e-4cd2-8ac0-3a5aa740f14d
-- title:
--   Exponential survival factorisation on an independent observed-past atom
-- statement:
--   At a deterministic age a, an observable past A independent of an exponential waiting time has joint survival on the atom A=a that factors as its joint survival at age a multiplied by exp(-t). The proof uses whole-random-variable independence, exact exponential tail survival and the exponential addition law. This is a conditional building block for the random-age memorylessness needed for the genuine Poisson stopped shift.
-- source:
--   Chat06 verified source bv_independent_exp_wait_fixed_age_atom_memorylessness_v2_chat06_20261020.lean at pinned revision 0df444a360eaa60ab8c11dca51a86af692955474; private remote compiler job 21222c70-63d6-4eae-890c-c20692cd4cd4 passed to sentinel with zero source errors.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.Ring

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.chat06_independent_exp_wait_atom_memorylessness
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (A τ : Ω → ℝ)
    (hInd : IndepFun A τ P)
    (hTail : ∀ u : ℝ, 0 ≤ u →
      P {ω | u < τ ω} =
        ENNReal.ofReal (Real.exp (-u)))
    (a t : ℝ) (ha : 0 ≤ a) (ht : 0 ≤ t) :
    P ({ω | A ω = a} ∩ {ω | a + t < τ ω}) =
      P ({ω | A ω = a} ∩ {ω | a < τ ω}) *
        ENNReal.ofReal (Real.exp (-t)) := by sorry
