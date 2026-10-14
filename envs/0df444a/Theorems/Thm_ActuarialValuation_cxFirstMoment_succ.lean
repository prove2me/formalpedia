-- Prove2me | Theorems.Thm_ActuarialValuation_cxFirstMoment_succ
-- name    : ActuarialValuation.cxFirstMoment_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:57:02.960303+00:00
-- url     : https://prove2.me/theorems/f18f19fc-7d10-4236-a585-c840305bdabe
-- title:
--   Finite count, severity and convolution transforms: cxFirstMoment_succ
-- statement:
--   A severity category contributes its monetary size times probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   μ_{n+1}=μ_n+n f_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxFirstMoment

namespace ActuarialValuation

theorem cxFirstMoment_succ (f : ℕ → ℝ) (n : ℕ) : cxFirstMoment f (n+1) = cxFirstMoment f n + (n:ℝ)*f n := by sorry

end ActuarialValuation
