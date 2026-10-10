-- Prove2me | Theorems.Thm_ActuarialValuation_cm1NonUnitCashflow_no_claims
-- name    : ActuarialValuation.cm1NonUnitCashflow_no_claims
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:59:07.155175+00:00
-- url     : https://prove2.me/theorems/ac38fc7b-136e-4a13-835c-fa5d89e050f9
-- title:
--   Projected profits and unit-linked funds: cm1NonUnitCashflow_no_claims
-- statement:
--   Without claims, projected non-unit cashflow consists of premium and charges less expenses. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B=0\Longrightarrow c=P+C-E
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1NonUnitCashflow

namespace ActuarialValuation

theorem cm1NonUnitCashflow_no_claims (P C E : ℝ) : cm1NonUnitCashflow P C E 0 = P+C-E := by sorry

end ActuarialValuation
