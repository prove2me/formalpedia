-- Prove2me | Theorems.Thm_ActuarialValuation_cxMass_succ
-- name    : ActuarialValuation.cxMass_succ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:54:45.897987+00:00
-- url     : https://prove2.me/theorems/70de4c1b-870e-468d-92a8-1cbbbaee4abd
-- title:
--   Finite count, severity and convolution transforms: cxMass_succ
-- statement:
--   Mass conservation includes the newly appended claim category. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   M_{n+1}=M_n+f_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxMass

namespace ActuarialValuation

theorem cxMass_succ (f : ℕ → ℝ) (n : ℕ) : cxMass f (n+1) = cxMass f n + f n := by sorry

end ActuarialValuation
