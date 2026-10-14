-- Prove2me | Theorems.Thm_ActuarialAnnuities_zero_guarantee
-- name    : ActuarialAnnuities.zero_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:59:20.05689+00:00
-- url     : https://prove2.me/theorems/312ba0d5-6acb-4d2e-a7de-0542b9d7744b
-- title:
--   Zero Guarantee
-- statement:
--   The no-guarantee boundary restores ordinary contingent payments.
--
--   Mathematical relation:
--
--   $$
--   E_{a,0,\delta}(j,k)=I_k(j+\delta),\quad j\ge a
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 159, Guaranteed annuities (Chapter 5, section 5.9). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive
import Definitions.Def_actuarial_bEntitlement

namespace ActuarialAnnuities

theorem zero_guarantee (a delta j k : ℕ) (hj : a ≤ j) : bEntitlement a 0 delta j k = bAlive k (j+delta) := by sorry

end ActuarialAnnuities
