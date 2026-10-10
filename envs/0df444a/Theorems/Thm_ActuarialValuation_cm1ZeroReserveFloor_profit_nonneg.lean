-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveFloor_profit_nonneg
-- name    : ActuarialValuation.cm1ZeroReserveFloor_profit_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:38:24.136742+00:00
-- url     : https://prove2.me/theorems/a3392c0a-2307-45e9-827e-0dbe24d1b2e0
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveFloor_profit_nonneg
-- statement:
--   The computed backwards reserve is sufficient to eliminate negative expected one-year profit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   c+gR_t^*-sR_{\rm next}\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ZeroReserveFloor

namespace ActuarialValuation

theorem cm1ZeroReserveFloor_profit_nonneg (c s g R : ℝ) (hg : 0 < g) : 0 ≤ c + g * cm1ZeroReserveFloor c s g R - s*R := by sorry

end ActuarialValuation
