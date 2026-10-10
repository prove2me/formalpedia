-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ReserveYearProfit_zero_reserves
-- name    : ActuarialValuation.cm1ReserveYearProfit_zero_reserves
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:59:28.001285+00:00
-- url     : https://prove2.me/theorems/3b1e935b-7dab-4bbe-b1c3-3f4bb22178d9
-- title:
--   Projected profits and unit-linked funds: cm1ReserveYearProfit_zero_reserves
-- statement:
--   Absent non-unit reserves, reserve-adjusted projected profit is the pure period cashflow. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   R\equiv0\Longrightarrow\Pi_t=c_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit

namespace ActuarialValuation

theorem cm1ReserveYearProfit_zero_reserves (c s g : ℕ → ℝ) (t : ℕ) : cm1ReserveYearProfit c s g (fun _ => 0) t = c t := by sorry

end ActuarialValuation
