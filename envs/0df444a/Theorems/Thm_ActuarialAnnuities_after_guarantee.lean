-- Prove2me | Theorems.Thm_ActuarialAnnuities_after_guarantee
-- name    : ActuarialAnnuities.after_guarantee
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:59:07.461979+00:00
-- url     : https://prove2.me/theorems/1ca8be9d-9bfe-4596-8df3-19aa05498ab0
-- title:
--   After Guarantee
-- statement:
--   After guarantee expiry each instalment requires survival at payment.
--
--   Mathematical relation:
--
--   $$
--   j\ge a+g\Longrightarrow E_{a,g,\delta}(j,k)=I_k(j+\delta)
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

theorem after_guarantee (a g delta j k : ℕ) (hj : a+g ≤ j) : bEntitlement a g delta j k = bAlive k (j+delta) := by sorry

end ActuarialAnnuities
