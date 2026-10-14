-- Prove2me | Theorems.Thm_ActuarialValuation_cxBernAggregateMass_nonneg
-- name    : ActuarialValuation.cxBernAggregateMass_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:58:10.973733+00:00
-- url     : https://prove2.me/theorems/79105ada-af29-4765-82fc-d86cbdc378de
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernAggregateMass_nonneg
-- statement:
--   Nonnegative count and severity masses produce a valid nonnegative aggregate atom. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   g_k≥0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass

namespace ActuarialValuation

theorem cxBernAggregateMass_nonneg (p0 p1 : ℝ) (f : ℕ → ℝ) (k : ℕ) (h0 : 0 ≤ p0) (h1 : 0 ≤ p1) (hf : 0 ≤ f k) (hf0 : 0 ≤ f 0) : 0 ≤ cxBernAggregateMass p0 p1 f k := by sorry

end ActuarialValuation
