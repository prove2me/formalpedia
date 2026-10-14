-- Prove2me | Theorems.Thm_ActuarialAnnuities_path_zero_term
-- name    : ActuarialAnnuities.path_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:59:51.712996+00:00
-- url     : https://prove2.me/theorems/aaf34281-9985-4ed9-b3c5-ec13b3d6fae7
-- title:
--   Path Zero Term
-- statement:
--   No payments can occur under a zero-duration annuity.
--
--   Mathematical relation:
--
--   $$
--   Z_k(n=0)=0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 157, Deferred annuities (Chapter 5, section 5.8). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bPathPV

namespace ActuarialAnnuities

theorem path_zero_term (h a g delta k : ℕ) (v : ℝ) (b : ℕ → ℝ) : bPathPV h a 0 g delta v b k = 0 := by sorry

end ActuarialAnnuities
