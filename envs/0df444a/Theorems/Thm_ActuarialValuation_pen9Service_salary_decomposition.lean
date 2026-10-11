-- Prove2me | Theorems.Thm_ActuarialValuation_pen9Service_salary_decomposition
-- name    : ActuarialValuation.pen9Service_salary_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:41:34.31947+00:00
-- url     : https://prove2.me/theorems/b2133c97-c364-4a8a-8cd7-703fbde98bf7
-- title:
--   Projected versus traditional unit credit and reserve recursion: pen9Service_salary_decomposition
-- statement:
--   The change in PUC separates genuine new-service cost from repricing previously accrued units due to a revised projected salary. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \Delta AL=NC_{new}+\alpha n\Delta S_R f
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9PUCNormalCost

namespace ActuarialValuation

theorem pen9Service_salary_decomposition (a old projected f : ℝ) (n : ℕ) : pen9PUC a projected f (n+1) - pen9PUC a old f n = pen9PUCNormalCost a projected f + a*(n:ℝ)*(projected-old)*f := by sorry

end ActuarialValuation
