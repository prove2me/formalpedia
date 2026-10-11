-- Prove2me | Theorems.Thm_ActuarialValuation_cxPairTransform_product
-- name    : ActuarialValuation.cxPairTransform_product
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T13:56:22.209975+00:00
-- url     : https://prove2.me/theorems/baeda216-9db3-4b38-8fe6-17777dd528a3
-- title:
--   Finite count, severity and convolution transforms: cxPairTransform_product
-- statement:
--   A full finite independent two-claim aggregate transform factors into separate probability generating functions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_{X+Y}=G_XG_Y
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxPairTransform

namespace ActuarialValuation

theorem cxPairTransform_product (f g : ℕ → ℝ) (n m : ℕ) (z : ℝ) : cxPairTransform f g n m z = cxPGF f n z * cxPGF g m z := by sorry

end ActuarialValuation
