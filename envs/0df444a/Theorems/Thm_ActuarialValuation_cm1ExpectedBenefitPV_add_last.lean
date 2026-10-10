-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ExpectedBenefitPV_add_last
-- name    : ActuarialValuation.cm1ExpectedBenefitPV_add_last
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:56:19.041986+00:00
-- url     : https://prove2.me/theorems/e8d41ca0-a4be-40d7-8562-b9b6b41fe539
-- title:
--   Gross premium equivalence: cm1ExpectedBenefitPV_add_last
-- statement:
--   Finite expected benefit PV recurses correctly when one extra payment term is appended. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_{N+1}=B_N+b_Nv_Np_N
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ExpectedBenefitPV

namespace ActuarialValuation

theorem cm1ExpectedBenefitPV_add_last (b d p : ℕ → ℝ) (N : ℕ) : cm1ExpectedBenefitPV b d p (N+1) = cm1ExpectedBenefitPV b d p N + b N*d N*p N := by sorry

end ActuarialValuation
