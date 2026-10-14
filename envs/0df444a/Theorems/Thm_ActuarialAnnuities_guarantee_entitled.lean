-- Prove2me | Theorems.Thm_ActuarialAnnuities_guarantee_entitled
-- name    : ActuarialAnnuities.guarantee_entitled
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:58:52.87017+00:00
-- url     : https://prove2.me/theorems/4194cb83-79f8-49a0-9b13-41715bbb530d
-- title:
--   Guarantee Entitled
-- statement:
--   An activated guarantee survives subsequent death and is payable to an estate.
--
--   Mathematical relation:
--
--   $$
--   j<a+g\Longrightarrow E_{a,g,\delta}(j,k)=I_k(a)
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

theorem guarantee_entitled (a g delta j k : ℕ) (hj : j < a+g) : bEntitlement a g delta j k = bAlive k a := by sorry

end ActuarialAnnuities
