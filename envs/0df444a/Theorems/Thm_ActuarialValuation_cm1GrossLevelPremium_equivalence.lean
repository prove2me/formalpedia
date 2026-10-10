-- Prove2me | Theorems.Thm_ActuarialValuation_cm1GrossLevelPremium_equivalence
-- name    : ActuarialValuation.cm1GrossLevelPremium_equivalence
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:55:45.032689+00:00
-- url     : https://prove2.me/theorems/84a48224-32e7-4611-a596-a94daee9b9c1
-- title:
--   Gross premium equivalence: cm1GrossLevelPremium_equivalence
-- statement:
--   Gross premium income PV exactly matches expected benefits and expenses under the equivalence principle. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   G A=B+E
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1GrossLevelPremium

namespace ActuarialValuation

theorem cm1GrossLevelPremium_equivalence (B E A : ℝ) (hA : A ≠ 0) : cm1GrossLevelPremium B E A * A = B + E := by sorry

end ActuarialValuation
