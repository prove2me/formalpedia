-- Prove2me | Theorems.Thm_ActuarialValuation_pen9UnitNormalCost_difference
-- name    : ActuarialValuation.pen9UnitNormalCost_difference
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:18.983996+00:00
-- url     : https://prove2.me/theorems/d9733afc-fcbc-4486-8fd6-6329169092fb
-- title:
--   Projected versus traditional unit credit and reserve recursion: pen9UnitNormalCost_difference
-- statement:
--   Per-year cost difference is the salary revaluation of one benefit unit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   NC^{PUC}-NC^{TUC}=\alpha(S_R-S_0)f
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUCNormalCost
import Definitions.Def_actuarial_pen9TUCNormalCost

namespace ActuarialValuation

theorem pen9UnitNormalCost_difference (a current projected f : ℝ) : pen9PUCNormalCost a projected f - pen9TUCNormalCost a current f = a*(projected-current)*f := by sorry

end ActuarialValuation
