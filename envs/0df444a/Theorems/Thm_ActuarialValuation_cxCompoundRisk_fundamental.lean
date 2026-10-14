-- Prove2me | Theorems.Thm_ActuarialValuation_cxCompoundRisk_fundamental
-- name    : ActuarialValuation.cxCompoundRisk_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T14:02:15.834553+00:00
-- url     : https://prove2.me/theorems/a5ba01a9-b30f-46a0-967a-26db7bbc785a
-- title:
--   Panjer adjustment with mass at zero: cxCompoundRisk_fundamental
-- statement:
--   The compound-risk capstone reconciles independent frequency/severity generating functions, probability normalisation, the aggregate zero atom, and the nontrivial Panjer zero-severity correction to the first positive aggregate mass. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G_S=G_N(G_X);(1-af_0)g_1=(a+b)f_1g_0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 393. S. David Promislow, Fundamentals of Actuarial Mathematics, third edition (2015), Chapter 21, https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml; H. H. Panjer, Recursive Evaluation of a Family of Compound Distributions (1981), https://doi.org/10.1017/S0515036100006796. Parent topic: Compound aggregate risk: convolution and probability generating functions, zero claim severity mass, first two moments and (a,b,0) Panjer recurrence. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/ftoc.xhtml

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cxPGF
import Definitions.Def_actuarial_cxMass
import Definitions.Def_actuarial_cxBernAggregateMass
import Definitions.Def_actuarial_cxBernAggregatePGF
import Definitions.Def_actuarial_cxBernCountPGF
import Definitions.Def_actuarial_cxPanjerA
import Definitions.Def_actuarial_cxPanjerB
import Definitions.Def_actuarial_cxPanjerAdjustment
import Definitions.Def_actuarial_cxPanjerFirstRHS

namespace ActuarialValuation

theorem cxCompoundRisk_fundamental (f : ℕ → ℝ) (n : ℕ) (p0 p1 z f1 : ℝ) (h0 : p0 ≠ 0) (hm : cxMass f n = 1) (hp : p0+p1=1) : (cxBernAggregatePGF p0 p1 f n z = cxBernCountPGF p0 p1 (cxPGF f n z)) ∧ (cxBernAggregatePGF p0 p1 f n 1 = 1) ∧ (cxBernAggregateMass p0 p1 f 0 = p0+p1*f 0) ∧ (cxBernAggregateMass p0 p1 (fun k => if k=0 then f 0 else if k=1 then f1 else 0) 1 * cxPanjerAdjustment (cxPanjerA p0 p1) (f 0) = cxPanjerFirstRHS (cxPanjerA p0 p1) (cxPanjerB p0 p1) f1 (p0+p1*f 0)) := by sorry

end ActuarialValuation
