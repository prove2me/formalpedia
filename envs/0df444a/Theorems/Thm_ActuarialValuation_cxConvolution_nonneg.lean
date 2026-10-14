-- Prove2me | Theorems.Thm_ActuarialValuation_cxConvolution_nonneg
-- name    : ActuarialValuation.cxConvolution_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:41.865966+00:00
-- url     : https://prove2.me/theorems/308d3b1f-8366-426f-900b-6651b90e25e6
-- title:
--   Finite count, severity and convolution transforms: cxConvolution_nonneg
-- statement:
--   The convolution of nonnegative probability masses is nonnegative. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (f*g)_k≥0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxConvolution

namespace ActuarialValuation

theorem cxConvolution_nonneg (f g : ℕ → ℝ) (k : ℕ) (hf : ∀ j ≤ k, 0 ≤ f j) (hg : ∀ j ≤ k, 0 ≤ g j) : 0 ≤ cxConvolution f g k := by sorry

end ActuarialValuation
