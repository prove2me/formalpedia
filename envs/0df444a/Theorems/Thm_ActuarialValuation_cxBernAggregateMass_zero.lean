-- Prove2me | Theorems.Thm_ActuarialValuation_cxBernAggregateMass_zero
-- name    : ActuarialValuation.cxBernAggregateMass_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:57:42.637794+00:00
-- url     : https://prove2.me/theorems/59a81450-de8a-4ae7-9e4e-5396d9a45d7d
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernAggregateMass_zero
-- statement:
--   The aggregate atom at zero includes both zero claim count and one claim of zero size. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_0=p_0+p_1f_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass

namespace ActuarialValuation

theorem cxBernAggregateMass_zero (p0 p1 : ℝ) (f : ℕ → ℝ) : cxBernAggregateMass p0 p1 f 0 = p0+p1*f 0 := by sorry

end ActuarialValuation
