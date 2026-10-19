-- Prove2me | Theorems.Thm_ActuarialAnnuities_root_reconciliation
-- name    : ActuarialAnnuities.root_reconciliation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:07:27.547462+00:00
-- url     : https://prove2.me/theorems/3c19b242-c132-471e-a2db-4611e563ad7b
-- title:
--   Root Reconciliation
-- statement:
--   Capstone derives both payment timings, both guarantee partitions, and exact due/arrears boundary from realised lifetime states.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_{\delta}]=V_{\delta}=V_{\delta,\text{guaranteed}}+V_{\delta,\text{post}},\quad\delta\in\{0,1\}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bSurvivalPV
import Definitions.Def_actuarial_bGuaranteedPV
import Definitions.Def_actuarial_bPostGuaranteePV
import Definitions.Def_actuarial_bLevel

namespace ActuarialAnnuities

theorem root_reconciliation (h a n g : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hn : ∀ k, 0 ≤ p k) (hp : bTotal h p = 1) (hv : 0 < v) (hv1 : v ≤ 1) : (bExpectedPV h a n g 0 v b p = bSurvivalPV h a n g 0 v b p) ∧ (bExpectedPV h a n g 1 v b p = bSurvivalPV h a n g 1 v b p) ∧ (bSurvivalPV h a n g 0 v b p = bGuaranteedPV h a n g 0 v b p+bPostGuaranteePV h a n g 0 v b p) ∧ (bSurvivalPV h a n g 1 v b p = bGuaranteedPV h a n g 1 v b p+bPostGuaranteePV h a n g 1 v b p) ∧ (bExpectedPV h 0 h 0 0 v (bLevel 1) p-bExpectedPV h 0 h 0 1 v (bLevel 1) p=1-v^h*bSurvival h p h) := by sorry

end ActuarialAnnuities
