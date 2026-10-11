-- Prove2me | Theorems.Thm_ActuarialValuation_cxTwoClaimMoment_zero_twocount
-- name    : ActuarialValuation.cxTwoClaimMoment_zero_twocount
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:59:45.384988+00:00
-- url     : https://prove2.me/theorems/693be21a-ef68-4c8c-bb7b-b80d6cec4bfd
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxTwoClaimMoment_zero_twocount
-- statement:
--   Without two-claim outcomes the aggregate raw second moment has no cross term. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E[S²]=p_1E[X²]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMoment

namespace ActuarialValuation

theorem cxTwoClaimMoment_zero_twocount (mu m2 p1 : ℝ) : cxTwoClaimMoment mu m2 p1 0 = p1*m2 := by sorry

end ActuarialValuation
