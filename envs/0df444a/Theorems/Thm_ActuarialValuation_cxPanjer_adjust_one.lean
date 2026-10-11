-- Prove2me | Theorems.Thm_ActuarialValuation_cxPanjer_adjust_one
-- name    : ActuarialValuation.cxPanjer_adjust_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:00:54.195981+00:00
-- url     : https://prove2.me/theorems/f34890ba-9aa1-4623-b71e-cd37a52a981a
-- title:
--   Panjer adjustment with mass at zero: cxPanjer_adjust_one
-- statement:
--   A zero a coefficient removes the zero-severity denominator correction. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   1-af_0=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerAdjustment

namespace ActuarialValuation

theorem cxPanjer_adjust_one (f0 : ℝ) : cxPanjerAdjustment 0 f0 = 1 := by sorry

end ActuarialValuation
