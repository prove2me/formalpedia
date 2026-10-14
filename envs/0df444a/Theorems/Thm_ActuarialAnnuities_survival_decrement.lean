-- Prove2me | Theorems.Thm_ActuarialAnnuities_survival_decrement
-- name    : ActuarialAnnuities.survival_decrement
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:58:40.722054+00:00
-- url     : https://prove2.me/theorems/767370be-0741-4124-a397-0eb5b55a87c7
-- title:
--   Survival Decrement
-- statement:
--   A final-survived-anniversary mass accounts for the fall in survival.
--
--   Mathematical relation:
--
--   $$
--   S_h(t)=p_t+S_h(t+1),\quad t\le h
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

theorem survival_decrement (h t : ℕ) (p : ℕ → ℝ) (ht : t ≤ h) : bSurvival h p t = p t + bSurvival h p (t+1) := by sorry

end ActuarialAnnuities
