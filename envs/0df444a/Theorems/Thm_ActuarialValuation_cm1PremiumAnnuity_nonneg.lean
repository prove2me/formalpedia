-- Prove2me | Theorems.Thm_ActuarialValuation_cm1PremiumAnnuity_nonneg
-- name    : ActuarialValuation.cm1PremiumAnnuity_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T21:55:34.096977+00:00
-- url     : https://prove2.me/theorems/e52dd5f2-79b9-4239-b162-b655ecb894fd
-- title:
--   Gross premium equivalence: cm1PremiumAnnuity_nonneg
-- statement:
--   Valid discount and in-force weights produce a nonnegative premium annuity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   A_P\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 8. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1PremiumAnnuity

namespace ActuarialValuation

theorem cm1PremiumAnnuity_nonneg (d p : ℕ → ℝ) (N : ℕ) (hd : ∀ t ∈ Finset.range N, 0 ≤ d t) (hp : ∀ t ∈ Finset.range N, 0 ≤ p t) : 0 ≤ cm1PremiumAnnuity d p N := by sorry

end ActuarialValuation
