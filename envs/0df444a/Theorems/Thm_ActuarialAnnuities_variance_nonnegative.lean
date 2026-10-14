-- Prove2me | Theorems.Thm_ActuarialAnnuities_variance_nonnegative
-- name    : ActuarialAnnuities.variance_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:07:00.064242+00:00
-- url     : https://prove2.me/theorems/fa28bd02-d9ff-4133-b093-21dea9f62630
-- title:
--   Variance Nonnegative
-- statement:
--   Valid probability masses make the actual central-square expectation nonnegative.
--
--   Mathematical relation:
--
--   $$
--   \operatorname{Var}(Z)\ge0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bTotal
import Definitions.Def_actuarial_bVariance

namespace ActuarialAnnuities

theorem variance_nonnegative (h a n g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (hp : bTotal h p = 1) (hn : ∀ k, 0 ≤ p k) : 0 ≤ bVariance h a n g delta v b p := by sorry

end ActuarialAnnuities
