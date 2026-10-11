-- Prove2me | Theorems.Thm_ActuarialValuation_cxPGF_succ
-- name    : ActuarialValuation.cxPGF_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:53:40.546986+00:00
-- url     : https://prove2.me/theorems/6480d569-6074-4aa9-8fc2-bb3273eb54ab
-- title:
--   Finite count, severity and convolution transforms: cxPGF_succ
-- statement:
--   Appending a new severity category appends only that probability-weighted monomial. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_{n+1}=G_n+f_nz^n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF

namespace ActuarialValuation

theorem cxPGF_succ (f : ℕ → ℝ) (n : ℕ) (z : ℝ) : cxPGF f (n+1) z = cxPGF f n z + f n*z^n := by sorry

end ActuarialValuation
