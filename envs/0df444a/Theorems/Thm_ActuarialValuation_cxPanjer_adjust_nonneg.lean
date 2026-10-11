-- Prove2me | Theorems.Thm_ActuarialValuation_cxPanjer_adjust_nonneg
-- name    : ActuarialValuation.cxPanjer_adjust_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:01:06.662361+00:00
-- url     : https://prove2.me/theorems/fb5136f6-1570-433c-bec7-af1c1e9c47a4
-- title:
--   Panjer adjustment with mass at zero: cxPanjer_adjust_nonneg
-- statement:
--   A positive no-claim probability and nonnegative claim probability make the corrected Bernoulli denominator strictly positive. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   1-af_0>0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPanjerA
import Definitions.Def_actuarial_cxPanjerAdjustment

namespace ActuarialValuation

theorem cxPanjer_adjust_nonneg (p0 p1 f0 : ℝ) (h0 : 0 < p0) (h1 : 0 ≤ p1) (hf : 0 ≤ f0) : 0 < cxPanjerAdjustment (cxPanjerA p0 p1) f0 := by sorry

end ActuarialValuation
