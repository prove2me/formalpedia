-- Prove2me | Theorems.Thm_ActuarialAnnuities_step_before
-- name    : ActuarialAnnuities.step_before
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:03:49.853985+00:00
-- url     : https://prove2.me/theorems/7c77aa57-dcdb-4171-a2b6-a6d54563d419
-- title:
--   Step Before
-- statement:
--   A step-up leaves preceding instalments at their first amount.
--
--   Mathematical relation:
--
--   $$
--   j<a+r\Longrightarrow b_j=c
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bStep

namespace ActuarialAnnuities

theorem step_before (a r j : ℕ) (c d : ℝ) (hj : j < a+r) : bStep a r c d j = c := by sorry

end ActuarialAnnuities
