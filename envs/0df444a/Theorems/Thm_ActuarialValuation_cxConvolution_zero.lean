-- Prove2me | Theorems.Thm_ActuarialValuation_cxConvolution_zero
-- name    : ActuarialValuation.cxConvolution_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:55:10.045265+00:00
-- url     : https://prove2.me/theorems/d4bdd3d8-825d-4778-ae13-185f8a147ba7
-- title:
--   Finite count, severity and convolution transforms: cxConvolution_zero
-- statement:
--   A zero aggregate is possible exactly when both independent severities are zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   h_0=f_0 g_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxConvolution

namespace ActuarialValuation

theorem cxConvolution_zero (f g : ℕ → ℝ) : cxConvolution f g 0 = f 0*g 0 := by sorry

end ActuarialValuation
