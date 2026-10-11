-- Prove2me | Theorems.Thm_ActuarialValuation_cxTwoClaimMean_zero
-- name    : ActuarialValuation.cxTwoClaimMean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:59:18.987405+00:00
-- url     : https://prove2.me/theorems/47796e88-1ca5-4905-b9fa-d31d2131a4f7
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxTwoClaimMean_zero
-- statement:
--   With no chance of two claims the aggregate mean is the Bernoulli count mean times severity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E[S]=p_1μ
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMean

namespace ActuarialValuation

theorem cxTwoClaimMean_zero (mean p1 : ℝ) : cxTwoClaimMean mean p1 0 = p1*mean := by sorry

end ActuarialValuation
