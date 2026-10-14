-- Prove2me | Theorems.Thm_ActuarialValuation_cxConvolution_comm
-- name    : ActuarialValuation.cxConvolution_comm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:26.627702+00:00
-- url     : https://prove2.me/theorems/54a7bc9e-344e-4bb9-8a09-6c7faa8b17e6
-- title:
--   Finite count, severity and convolution transforms: cxConvolution_comm
-- statement:
--   Adding two independent integer-valued severities is symmetric in their laws. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   f*g=g*f
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxConvolution

namespace ActuarialValuation

theorem cxConvolution_comm (f g : ℕ → ℝ) (k : ℕ) : cxConvolution f g k = cxConvolution g f k := by sorry

end ActuarialValuation
