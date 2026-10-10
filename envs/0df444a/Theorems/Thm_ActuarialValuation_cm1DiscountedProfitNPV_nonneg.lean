-- Prove2me | Theorems.Thm_ActuarialValuation_cm1DiscountedProfitNPV_nonneg
-- name    : ActuarialValuation.cm1DiscountedProfitNPV_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:00:05.997999+00:00
-- url     : https://prove2.me/theorems/87fa9ccc-6a8c-419f-b6e5-2a076141a6c6
-- title:
--   Projected profits and unit-linked funds: cm1DiscountedProfitNPV_nonneg
-- statement:
--   Nonnegative future profits and nonnegative risk discount weights have nonnegative NPV. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Pi_t,v_t\ge0\Longrightarrow NPV\ge0
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 10. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1DiscountedProfitNPV

namespace ActuarialValuation

theorem cm1DiscountedProfitNPV_nonneg (profits discount : ℕ → ℝ) (N : ℕ) (hp : ∀ t ∈ Finset.range N, 0 ≤ profits t) (hd : ∀ t ∈ Finset.range N, 0 ≤ discount t) : 0 ≤ cm1DiscountedProfitNPV profits discount N := by sorry

end ActuarialValuation
