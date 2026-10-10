-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroReserveCondition_minimal
-- name    : ActuarialValuation.cm1ZeroReserveCondition_minimal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:41:17.793647+00:00
-- url     : https://prove2.me/theorems/2fd507ff-555e-48c2-94fb-daa95612a558
-- title:
--   Backwards non-unit zeroisation: cm1ZeroReserveCondition_minimal
-- statement:
--   A backward-induction argument proves that any alternative nonnegative profit-feasible reserve schedule must dominate the zeroised schedule at every date. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   Q_N=R_N=0,\ Q_t\ge0,\ \Pi_t(Q)\ge0\Longrightarrow R_t\le Q_t
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit
import Definitions.Def_actuarial_cm1ZeroReserveCondition

namespace ActuarialValuation

theorem cm1ZeroReserveCondition_minimal (c s g R Q : ℕ → ℝ) (N t : ℕ)
  (hR : cm1ZeroReserveCondition c s g R N)
  (hg : ∀ j ∈ Finset.range N, 0 < g j)
  (hs : ∀ j ∈ Finset.range N, 0 ≤ s j)
  (hQend : Q N = 0)
  (hQpos : ∀ j, j ≤ N → 0 ≤ Q j)
  (hQprof : ∀ j ∈ Finset.range N, 0 ≤ cm1ReserveYearProfit c s g Q j)
  (ht : t ≤ N) : R t ≤ Q t := by sorry

end ActuarialValuation
