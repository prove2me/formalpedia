-- Prove2me | Theorems.Thm_ActuarialAnnuities_expectation_add
-- name    : ActuarialAnnuities.expectation_add
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:01:28.753037+00:00
-- url     : https://prove2.me/theorems/4d9e2c67-abd8-4916-8ad8-8e922907ca8c
-- title:
--   Expectation Add
-- statement:
--   Expected values of combined cashflow streams are additive.
--
--   Mathematical relation:
--
--   $$
--   \mathbb E[Z_{b+c}]=\mathbb E[Z_b]+\mathbb E[Z_c]
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bExpectedPV

namespace ActuarialAnnuities

theorem expectation_add (h a n g delta : ℕ) (v : ℝ) (b c p : ℕ → ℝ) : bExpectedPV h a n g delta v (fun j => b j+c j) p = bExpectedPV h a n g delta v b p+bExpectedPV h a n g delta v c p := by sorry

end ActuarialAnnuities
