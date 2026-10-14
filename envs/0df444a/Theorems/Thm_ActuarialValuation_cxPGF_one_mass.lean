-- Prove2me | Theorems.Thm_ActuarialValuation_cxPGF_one_mass
-- name    : ActuarialValuation.cxPGF_one_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:54:15.762985+00:00
-- url     : https://prove2.me/theorems/c59fb7c5-e629-4b64-acec-5e5f62a56c0e
-- title:
--   Finite count, severity and convolution transforms: cxPGF_one_mass
-- statement:
--   The transform at one gives the total probability mass. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_X(1)=Σ f_j
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxMass

namespace ActuarialValuation

theorem cxPGF_one_mass (f : ℕ → ℝ) (n : ℕ) : cxPGF f n 1 = cxMass f n := by sorry

end ActuarialValuation
