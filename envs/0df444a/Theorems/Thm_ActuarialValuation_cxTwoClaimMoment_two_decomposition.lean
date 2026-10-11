-- Prove2me | Theorems.Thm_ActuarialValuation_cxTwoClaimMoment_two_decomposition
-- name    : ActuarialValuation.cxTwoClaimMoment_two_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:59:58.425035+00:00
-- url     : https://prove2.me/theorems/37422cf7-c982-459a-982b-85ae3ae3ba53
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxTwoClaimMoment_two_decomposition
-- statement:
--   The two-claim cross product adds twice the product of the severity means. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   m_{2,S}=E[N]m_{2,X}+2p_2μ²
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxTwoClaimMoment

namespace ActuarialValuation

theorem cxTwoClaimMoment_two_decomposition (mu m2 p1 p2 : ℝ) : cxTwoClaimMoment mu m2 p1 p2 = (p1+2*p2)*m2+2*p2*mu^2 := by sorry

end ActuarialValuation
