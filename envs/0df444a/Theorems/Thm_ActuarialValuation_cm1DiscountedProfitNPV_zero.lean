-- Prove2me | Theorems.Thm_ActuarialValuation_cm1DiscountedProfitNPV_zero
-- name    : ActuarialValuation.cm1DiscountedProfitNPV_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:59:41.89869+00:00
-- url     : https://prove2.me/theorems/abd438d7-5542-44ab-a132-6db7ec8660e7
-- title:
--   Projected profits and unit-linked funds: cm1DiscountedProfitNPV_zero
-- statement:
--   No future profit payments produce zero risk-discounted profit PV. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   NPV(0)=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DiscountedProfitNPV

namespace ActuarialValuation

theorem cm1DiscountedProfitNPV_zero (profits discount : ℕ → ℝ) : cm1DiscountedProfitNPV profits discount 0 = 0 := by sorry

end ActuarialValuation
