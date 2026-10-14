-- Prove2me | Theorems.Thm_ActuarialValuation_cxTwoClaimMean_scale
-- name    : ActuarialValuation.cxTwoClaimMean_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:59:30.589552+00:00
-- url     : https://prove2.me/theorems/752c270c-9117-409b-bfc8-7164f6a8cb97
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxTwoClaimMean_scale
-- statement:
--   Scaling individual claims scales the aggregate expected loss. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E[cS]=cE[S]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMean

namespace ActuarialValuation

theorem cxTwoClaimMean_scale (mean p1 p2 c : ℝ) : cxTwoClaimMean (c*mean) p1 p2 = c*cxTwoClaimMean mean p1 p2 := by sorry

end ActuarialValuation
