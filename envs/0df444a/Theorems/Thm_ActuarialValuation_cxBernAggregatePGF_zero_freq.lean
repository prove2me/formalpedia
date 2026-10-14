-- Prove2me | Theorems.Thm_ActuarialValuation_cxBernAggregatePGF_zero_freq
-- name    : ActuarialValuation.cxBernAggregatePGF_zero_freq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:58:22.826342+00:00
-- url     : https://prove2.me/theorems/5c8341f7-7372-4432-a47c-965997a15b22
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernAggregatePGF_zero_freq
-- statement:
--   No claims means only the probability of zero count contributes. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_S=p_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregatePGF

namespace ActuarialValuation

theorem cxBernAggregatePGF_zero_freq (p0 : ℝ) (f : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxBernAggregatePGF p0 0 f n z = p0 := by sorry

end ActuarialValuation
