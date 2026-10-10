-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProfitMargin_cancel
-- name    : ActuarialValuation.cm1ProfitMargin_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:00:33.206801+00:00
-- url     : https://prove2.me/theorems/b92904a5-4a39-4659-a0ec-587b68fd28dc
-- title:
--   Projected profits and unit-linked funds: cm1ProfitMargin_cancel
-- statement:
--   Profit margin times premium PV recovers profit PV when the denominator is nonzero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   mP=NPV
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProfitMargin

namespace ActuarialValuation

theorem cm1ProfitMargin_cancel (profitPV premiumPV : ℝ) (h : premiumPV ≠ 0) : cm1ProfitMargin profitPV premiumPV * premiumPV = profitPV := by sorry

end ActuarialValuation
