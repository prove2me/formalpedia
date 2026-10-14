-- Prove2me | Theorems.Thm_ActuarialValuation_pen9ActiveProbability_bounds
-- name    : ActuarialValuation.pen9ActiveProbability_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:45.670976+00:00
-- url     : https://prove2.me/theorems/b54b03ad-d094-4b71-a733-cc52f66ca398
-- title:
--   Service-table exits, survivor and deferred benefits: pen9ActiveProbability_bounds
-- statement:
--   Valid cause probabilities with total exit mass no greater than one give a valid active-retention probability. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   0\le p^a\le1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitMass
import Definitions.Def_actuarial_pen9ActiveProbability

namespace ActuarialValuation

theorem pen9ActiveProbability_bounds (w d i r : ℝ) (hw : 0 ≤ w) (hd : 0 ≤ d) (hi : 0 ≤ i) (hr : 0 ≤ r) (h : pen9ExitMass w d i r ≤ 1) : 0 ≤ pen9ActiveProbability w d i r ∧ pen9ActiveProbability w d i r ≤ 1 := by sorry

end ActuarialValuation
