-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ExpectedBenefitPV_zero
-- name    : ActuarialValuation.cm1ExpectedBenefitPV_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:54:18.911272+00:00
-- url     : https://prove2.me/theorems/3e2a3dec-3a80-441b-8084-8e1f2c6f6a7f
-- title:
--   Gross premium equivalence: cm1ExpectedBenefitPV_zero
-- statement:
--   No future benefit scenarios yield zero expected benefit present value. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B(0)=0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedBenefitPV

namespace ActuarialValuation

theorem cm1ExpectedBenefitPV_zero (b d p : ℕ → ℝ) : cm1ExpectedBenefitPV b d p 0 = 0 := by sorry

end ActuarialValuation
