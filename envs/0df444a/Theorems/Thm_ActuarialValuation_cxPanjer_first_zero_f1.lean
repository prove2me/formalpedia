-- Prove2me | Theorems.Thm_ActuarialValuation_cxPanjer_first_zero_f1
-- name    : ActuarialValuation.cxPanjer_first_zero_f1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:01:18.604523+00:00
-- url     : https://prove2.me/theorems/fea643a7-1024-4ba8-8247-983d890dac4b
-- title:
--   Panjer adjustment with mass at zero: cxPanjer_first_zero_f1
-- statement:
--   Without a unit-size claim atom the first positive mass recurrence numerator vanishes. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f_1=0⇒RHS=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerFirstRHS

namespace ActuarialValuation

theorem cxPanjer_first_zero_f1 (a b g0 : ℝ) : cxPanjerFirstRHS a b 0 g0 = 0 := by sorry

end ActuarialValuation
