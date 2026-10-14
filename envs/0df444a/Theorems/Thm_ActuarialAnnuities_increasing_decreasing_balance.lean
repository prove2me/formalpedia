-- Prove2me | Theorems.Thm_ActuarialAnnuities_increasing_decreasing_balance
-- name    : ActuarialAnnuities.increasing_decreasing_balance
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:03:35.555179+00:00
-- url     : https://prove2.me/theorems/3f8e5065-ea62-4631-bbee-25711a5d7295
-- title:
--   Increasing Decreasing Balance
-- statement:
--   Opposed linear benefit patterns add to a level n plus one.
--
--   Mathematical relation:
--
--   $$
--   b_j^{\text{increasing}}+b_j^{\text{decreasing}}=n+1
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 161, Increasing annuities (Chapter 5, section 5.10). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bIncreasing
import Definitions.Def_actuarial_bDecreasing

namespace ActuarialAnnuities

theorem increasing_decreasing_balance (a n j : ℕ) (ha : a ≤ j) (hj : j < a+n) : bIncreasing a j+bDecreasing a n j = (n+1 : ℕ) := by sorry

end ActuarialAnnuities
