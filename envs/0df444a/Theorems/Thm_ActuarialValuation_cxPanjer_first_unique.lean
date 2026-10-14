-- Prove2me | Theorems.Thm_ActuarialValuation_cxPanjer_first_unique
-- name    : ActuarialValuation.cxPanjer_first_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:01:44.239259+00:00
-- url     : https://prove2.me/theorems/ae92e6e8-5ef5-43d4-a085-852e822d8a09
-- title:
--   Panjer adjustment with mass at zero: cxPanjer_first_unique
-- statement:
--   The correctly adjusted first positive mass is uniquely determined when the Panjer denominator does not vanish. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_1=RHS/(1-af_0)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerAdjustment
import Definitions.Def_actuarial_cxPanjerFirstRHS

namespace ActuarialValuation

theorem cxPanjer_first_unique (a b f0 f1 g0 g1 : ℝ) (h : cxPanjerAdjustment a f0 ≠ 0) (heq : g1*cxPanjerAdjustment a f0 = cxPanjerFirstRHS a b f1 g0) : g1 = cxPanjerFirstRHS a b f1 g0 / cxPanjerAdjustment a f0 := by sorry

end ActuarialValuation
