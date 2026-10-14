-- Prove2me | Theorems.Thm_ActuarialAnnuities_expectation_zero_term
-- name    : ActuarialAnnuities.expectation_zero_term
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:00:50.302569+00:00
-- url     : https://prove2.me/theorems/5261a6a4-efde-493c-9778-22222987c5e9
-- title:
--   Expectation Zero Term
-- statement:
--   A zero-duration contract's actual expected cashflow is zero.
--
--   Mathematical relation:
--
--   $$
--   n=0\Longrightarrow\mathbb E[Z]=0
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV

namespace ActuarialAnnuities

theorem expectation_zero_term (h a g delta : ℕ) (v : ℝ) (b p : ℕ → ℝ) : bExpectedPV h a 0 g delta v b p = 0 := by sorry

end ActuarialAnnuities
