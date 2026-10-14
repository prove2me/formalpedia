-- Prove2me | Theorems.Thm_ActuarialAnnuities_udd_final
-- name    : ActuarialAnnuities.udd_final
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-12T20:05:42.848849+00:00
-- url     : https://prove2.me/theorems/4efb5f2d-360f-4e08-84c6-fb195fc965bd
-- title:
--   Udd Final
-- statement:
--   UDD exactly reproduces second annual survival endpoint.
--
--   Mathematical relation:
--
--   $$
--   S(u+1)=S(u+1)
--   $$
--
--   Timing and admissibility conditions are the exact conditions of the declaration. Cash amounts are per instalment and present values are at valuation time zero.
-- source:
--   Original derived finite-cashflow result, contextual source page 165, UDD approximation (Chapter 5, section 5.11.2). D. C. M. Dickson, M. R. Hardy and H. R. Waters (2020), Actuarial Mathematics for Life Contingent Risks, third edition, Cambridge University Press. https://www.cambridge.org/highereducation/books/actuarial-mathematics-for-life-contingent-risks/281DA4E8D523A6B23280ADC3D165AFDA/contents/4EB4E907782E2CD9CF0447D8F5DF1F6E. The cited page identifies the surrounding topic, not a numbered theorem with this exact Lean signature.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_bUDD

namespace ActuarialAnnuities

theorem udd_final (s0 s1 : ℝ) : bUDD s0 s1 1 = s1 := by sorry

end ActuarialAnnuities
