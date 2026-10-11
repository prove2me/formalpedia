-- Prove2me | Theorems.Thm_ActuarialValuation_cxBernCountPGF_one
-- name    : ActuarialValuation.cxBernCountPGF_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:59:03.288354+00:00
-- url     : https://prove2.me/theorems/d77c0c3c-2d73-4a6b-a9ff-3de971789670
-- title:
--   Bernoulli claim counts, zero claims and aggregate moments: cxBernCountPGF_one
-- statement:
--   The frequency PGF is normalised under its stated probability condition. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_N(1)=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernCountPGF

namespace ActuarialValuation

theorem cxBernCountPGF_one (p0 p1 : ℝ) (h : p0+p1=1) : cxBernCountPGF p0 p1 1 = 1 := by sorry

end ActuarialValuation
