-- Prove2me | Theorems.Thm_ActuarialAnnuities_survival_initial
-- name    : ActuarialAnnuities.survival_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:57:27.942756+00:00
-- url     : https://prove2.me/theorems/7b070a99-6b82-4ac9-9c5b-ce2693326e9f
-- title:
--   Survival Initial
-- statement:
--   The first survival probability is the sum of lifetime-state masses.
--
--   Mathematical relation:
--
--   $$
--   S_h(0)=M_h
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

theorem survival_initial (h : ℕ) (p : ℕ → ℝ) : bSurvival h p 0 = bTotal h p := by sorry

end ActuarialAnnuities
