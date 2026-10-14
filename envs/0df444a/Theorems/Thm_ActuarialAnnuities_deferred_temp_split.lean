-- Prove2me | Theorems.Thm_ActuarialAnnuities_deferred_temp_split
-- name    : ActuarialAnnuities.deferred_temp_split
-- status  : Open
-- author  : @WillR
-- created : 2026-10-12T20:04:51.498335+00:00
-- url     : https://prove2.me/theorems/595458ff-9674-4448-b9ce-01e28183cbf0
-- title:
--   Deferred Temp Split
-- statement:
--   Adjacent deferred temporary periods contain exactly the original scheduled payments.
--
--   Mathematical relation:
--
--   $$
--   V_{a:n+m}=V_{a:n}+V_{a+n:m}
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 157, Deferred annuities (Chapter 5, section 5.8). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bSurvivalPV

namespace ActuarialAnnuities

theorem deferred_temp_split (h a n m delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) (ha : a+n+m ≤ h) : bSurvivalPV h a (n+m) 0 delta v b p = bSurvivalPV h a n 0 delta v b p+bSurvivalPV h (a+n) m 0 delta v b p := by sorry

end ActuarialAnnuities
