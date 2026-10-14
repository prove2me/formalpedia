-- Prove2me | Theorems.Thm_ActuarialValuation_cxPGF_scale
-- name    : ActuarialValuation.cxPGF_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:54:01.375517+00:00
-- url     : https://prove2.me/theorems/eb0d0e02-f9de-4793-a210-39d329ae5c92
-- title:
--   Finite count, severity and convolution transforms: cxPGF_scale
-- statement:
--   The generating polynomial is linear in mass weights. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_{cf}=cG_f
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF

namespace ActuarialValuation

theorem cxPGF_scale (f : ℕ → ℝ) (n : ℕ) (z c : ℝ) : cxPGF (fun k => c*f k) n z = c*cxPGF f n z := by sorry

end ActuarialValuation
