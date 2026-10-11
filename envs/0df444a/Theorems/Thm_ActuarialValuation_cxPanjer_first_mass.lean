-- Prove2me | Theorems.Thm_ActuarialValuation_cxPanjer_first_mass
-- name    : ActuarialValuation.cxPanjer_first_mass
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T14:01:30.272803+00:00
-- url     : https://prove2.me/theorems/7cfdc8e8-2c5c-4408-9475-41ae97339680
-- title:
--   Panjer adjustment with mass at zero: cxPanjer_first_mass
-- statement:
--   For a genuine Bernoulli count, the zero-claim-size Panjer denominator reconciles to the independently defined first strictly positive aggregate atom. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (1-af_0)g_1=(a+b)f_1g_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxBernAggregateMass
import Definitions.Def_actuarial_cxPanjerA
import Definitions.Def_actuarial_cxPanjerB
import Definitions.Def_actuarial_cxPanjerAdjustment
import Definitions.Def_actuarial_cxPanjerFirstRHS

namespace ActuarialValuation

theorem cxPanjer_first_mass (p0 p1 f0 f1 : ℝ) (hp0 : p0 ≠ 0) : cxBernAggregateMass p0 p1 (fun k => if k=0 then f0 else if k=1 then f1 else 0) 1 * cxPanjerAdjustment (cxPanjerA p0 p1) f0 = cxPanjerFirstRHS (cxPanjerA p0 p1) (cxPanjerB p0 p1) f1 (p0+p1*f0) := by sorry

end ActuarialValuation
