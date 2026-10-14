-- Prove2me | Theorems.Thm_ActuarialAnnuities_due_arrears_boundary
-- name    : ActuarialAnnuities.due_arrears_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:05:06.428278+00:00
-- url     : https://prove2.me/theorems/aa113256-67ce-414c-a3ec-16108d44f236
-- title:
--   Due Arrears Boundary
-- statement:
--   Finite due-minus-arrears difference includes the contingent terminal arrears payment.
--
--   Mathematical relation:
--
--   $$
--   \ddot a_{\overline{h}|}-a_{\overline{h}|}=1-v^{h}S_h(h)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 148, Immediate life annuities (Chapter 5, section 5.4.3). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival
import Definitions.Def_actuarial_bExpectedPV
import Definitions.Def_actuarial_bLevel

namespace ActuarialAnnuities

theorem due_arrears_boundary (h : ℕ) (v : ℝ) (p : ℕ → ℝ) (hp : bTotal h p = 1) : bExpectedPV h 0 h 0 0 v (bLevel 1) p-bExpectedPV h 0 h 0 1 v (bLevel 1) p = 1-v^h*bSurvival h p h := by sorry

end ActuarialAnnuities
