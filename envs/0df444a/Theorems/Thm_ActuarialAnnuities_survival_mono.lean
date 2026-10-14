-- Prove2me | Theorems.Thm_ActuarialAnnuities_survival_mono
-- name    : ActuarialAnnuities.survival_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:58:22.71598+00:00
-- url     : https://prove2.me/theorems/8c00245a-855b-430d-885f-c24dd8220d7b
-- title:
--   Survival Mono
-- statement:
--   Survival declines as the required anniversary increases.
--
--   Mathematical relation:
--
--   $$
--   t\le u\Longrightarrow S_h(u)\le S_h(t)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvival

namespace ActuarialAnnuities

theorem survival_mono (h t u : ℕ) (p : ℕ → ℝ) (hp : ∀ k, 0 ≤ p k) (htu : t ≤ u) : bSurvival h p u ≤ bSurvival h p t := by sorry

end ActuarialAnnuities
