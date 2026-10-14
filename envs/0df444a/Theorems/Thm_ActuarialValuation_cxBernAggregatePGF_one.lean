-- Prove2me | Theorems.Thm_ActuarialValuation_cxBernAggregatePGF_one
-- name    : ActuarialValuation.cxBernAggregatePGF_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:58:51.994112+00:00
-- url     : https://prove2.me/theorems/f58abf49-0997-4e03-9ffd-d78747ea3ce5
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernAggregatePGF_one
-- statement:
--   Normalised severities and frequency produce a proper aggregate generating function. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_S(1)=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxMass
import Definitions.Def_actuarial_cxBernAggregatePGF

namespace ActuarialValuation

theorem cxBernAggregatePGF_one (p0 p1 : ℝ) (f : ℕ → ℝ) (n : ℕ) (hf : cxMass f n = 1) (hp : p0+p1=1) : cxBernAggregatePGF p0 p1 f n 1 = 1 := by sorry

end ActuarialValuation
