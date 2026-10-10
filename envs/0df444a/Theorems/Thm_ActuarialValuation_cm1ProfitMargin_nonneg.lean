-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProfitMargin_nonneg
-- name    : ActuarialValuation.cm1ProfitMargin_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:00:43.688978+00:00
-- url     : https://prove2.me/theorems/0d66b50e-9727-4974-9ab6-0a596a6e6f8e
-- title:
--   Projected profits and unit-linked funds: cm1ProfitMargin_nonneg
-- statement:
--   Profit margin is nonnegative if projected profit is nonnegative and the premium base positive. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   NPV\ge0,\ PV(P)>0\Longrightarrow m\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProfitMargin

namespace ActuarialValuation

theorem cm1ProfitMargin_nonneg (P V : ℝ) (hp : 0 ≤ P) (hV : 0 < V) : 0 ≤ cm1ProfitMargin P V := by sorry

end ActuarialValuation
