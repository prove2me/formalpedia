-- Prove2me | Theorems.Thm_ActuarialAnnuities_alive_later_mono
-- name    : ActuarialAnnuities.alive_later_mono
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:57:17.698273+00:00
-- url     : https://prove2.me/theorems/a8ffbfa1-acb7-49b2-a582-81d1e8bc233f
-- title:
--   Alive Later Mono
-- statement:
--   Surviving a later anniversary implies survival at an earlier one.
--
--   Mathematical relation:
--
--   $$
--   t\le u\Longrightarrow I_k(u)\le I_k(t)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive

namespace ActuarialAnnuities

theorem alive_later_mono (k t u : ℕ) (htu : t ≤ u) : bAlive k u ≤ bAlive k t := by sorry

end ActuarialAnnuities
