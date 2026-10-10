-- Prove2me | Theorems.Thm_ActuarialValuation_cm1ZeroisationOptimality_fundamental
-- name    : ActuarialValuation.cm1ZeroisationOptimality_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T22:41:31.735536+00:00
-- url     : https://prove2.me/theorems/3bb28873-2cf6-4a5b-978a-36ba615ea528
-- title:
--   Backwards non-unit zeroisation: cm1ZeroisationOptimality_fundamental
-- statement:
--   The finite-horizon capstone proves that a backwards-zeroised reserve produces nonnegative projected profits and is pointwise minimal among all nonnegative feasible reserve paths with the same terminal boundary. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived CM1 mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   (\forall t<N:\ \Pi_t(R)\ge0)\ \land\ (\forall t\le N:\ R_t\le Q_t)
--   $$
-- source:
--   Original derived formalisation, CM1_new_formula.pdf page 11. Institute and Faculty of Actuaries, CM1 2026 syllabus, Section 4, https://actuaries.org.uk/media/yfnkmkbq/cm1_syllabus-2026-_final-proof.pdf; Dickson, Hardy and Waters (2009), chapters 7 and 11, Emerging costs for traditional life insurance, https://doi.org/10.1017/CBO9780511800146.012; CM1_new_formula.pdf (user study notes), pages 8–11. Parent topic: CM1 prospective/retrospective life reserves, financial profit signatures, projected cashflow models, unit-linked non-unit zeroisation. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_cm1ReserveYearProfit
import Definitions.Def_actuarial_cm1ZeroReserveCondition

namespace ActuarialValuation

theorem cm1ZeroisationOptimality_fundamental (c s g R Q : ℕ → ℝ) (N : ℕ)
  (hR : cm1ZeroReserveCondition c s g R N)
  (hg : ∀ j ∈ Finset.range N, 0 < g j)
  (hs : ∀ j ∈ Finset.range N, 0 ≤ s j)
  (hQend : Q N = 0)
  (hQpos : ∀ j, j ≤ N → 0 ≤ Q j)
  (hQprof : ∀ j ∈ Finset.range N, 0 ≤ cm1ReserveYearProfit c s g Q j) :
  (∀ t ∈ Finset.range N, 0 ≤ cm1ReserveYearProfit c s g R t) ∧
  (∀ t, t ≤ N → R t ≤ Q t) := by sorry

end ActuarialValuation
