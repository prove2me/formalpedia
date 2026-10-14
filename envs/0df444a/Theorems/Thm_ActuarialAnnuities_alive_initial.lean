-- Prove2me | Theorems.Thm_ActuarialAnnuities_alive_initial
-- name    : ActuarialAnnuities.alive_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T19:50:39.173982+00:00
-- url     : https://prove2.me/theorems/fa34b6bc-2d33-4ec0-88c6-bb65c4d42099
-- title:
--   Alive Initial
-- statement:
--   Every possible state survives the zero anniversary.
--
--   Mathematical relation:
--
--   $$
--   I_k(0)=1
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 143, Annual life annuities (Chapter 5, section 5.4). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bAlive

namespace ActuarialAnnuities

theorem alive_initial (k : ℕ) : bAlive k 0 = 1 := by sorry

end ActuarialAnnuities
