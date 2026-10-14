-- Prove2me | Theorems.Thm_ActuarialAnnuities_step_after
-- name    : ActuarialAnnuities.step_after
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:04:01.30677+00:00
-- url     : https://prove2.me/theorems/542a1417-9e6b-4924-9eaa-f26f6480d13f
-- title:
--   Step After
-- statement:
--   The new step level begins at the specified first payment.
--
--   Mathematical relation:
--
--   $$
--   j\ge a+r\Longrightarrow b_j=d
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bStep

namespace ActuarialAnnuities

theorem step_after (a r j : ℕ) (c d : ℝ) (hj : a+r ≤ j) : bStep a r c d j = d := by sorry

end ActuarialAnnuities
