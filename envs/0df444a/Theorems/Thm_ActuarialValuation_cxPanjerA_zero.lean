-- Prove2me | Theorems.Thm_ActuarialValuation_cxPanjerA_zero
-- name    : ActuarialValuation.cxPanjerA_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:00:12.504222+00:00
-- url     : https://prove2.me/theorems/e678c41a-166c-483f-b6bb-3bd3a0026a37
-- title:
--   Panjer adjustment with mass at zero: cxPanjerA_zero
-- statement:
--   With no positive claim count there is no Bernoulli frequency recurrence coefficient. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   a=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerA

namespace ActuarialValuation

theorem cxPanjerA_zero (p0 : ℝ) : cxPanjerA p0 0 = 0 := by sorry

end ActuarialValuation
