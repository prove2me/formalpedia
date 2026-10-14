-- Prove2me | Theorems.Thm_ActuarialValuation_cxPairTransform_unit
-- name    : ActuarialValuation.cxPairTransform_unit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T13:56:34.082512+00:00
-- url     : https://prove2.me/theorems/c2d13e88-4e22-4b01-9b7a-b82f7f78a58a
-- title:
--   Finite count, severity and convolution transforms: cxPairTransform_unit
-- statement:
--   The independent joint probability law normalises when each marginal mass normalises. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   E[1]=P_f P_g
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPairTransform
import Definitions.Def_actuarial_cxMass

namespace ActuarialValuation

theorem cxPairTransform_unit (f g : ℕ → ℝ) (n m : ℕ) : cxPairTransform f g n m 1 = cxMass f n * cxMass g m := by sorry

end ActuarialValuation
