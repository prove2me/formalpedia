-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ProspectiveCashReserve_antitone_premiums
-- name    : ActuarialValuation.cm1ProspectiveCashReserve_antitone_premiums
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:57:12.220985+00:00
-- url     : https://prove2.me/theorems/e8a13dd2-f222-417f-8659-a7d47027885a
-- title:
--   Prospective reserve and mortality profit: cm1ProspectiveCashReserve_antitone_premiums
-- statement:
--   Higher future premium income reduces the net prospective reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   P_1\le P_2\Longrightarrow V(P_2)\le V(P_1)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 9. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ProspectiveCashReserve

namespace ActuarialValuation

theorem cm1ProspectiveCashReserve_antitone_premiums (B E P₁ P₂ : ℝ) (h : P₁ ≤ P₂) : cm1ProspectiveCashReserve B E P₂ ≤ cm1ProspectiveCashReserve B E P₁ := by sorry

end ActuarialValuation
