-- Prove2me | Theorems.Thm_ActuarialAnnuities_survival_nonneg
-- name    : ActuarialAnnuities.survival_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:58:08.292986+00:00
-- url     : https://prove2.me/theorems/be8e4067-ec5f-467e-97f0-ec9ed813419e
-- title:
--   Survival Nonneg
-- statement:
--   Nonnegative probability masses give nonnegative survival.
--
--   Mathematical relation:
--
--   $$
--   p_k\ge0\Longrightarrow S_h(t)\ge0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

theorem survival_nonneg (h t : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) : 0 ≤ bSurvival h p t := by sorry

end ActuarialAnnuities
