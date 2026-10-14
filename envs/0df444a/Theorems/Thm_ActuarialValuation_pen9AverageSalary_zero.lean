-- Prove2me | Theorems.Thm_ActuarialValuation_pen9AverageSalary_zero
-- name    : ActuarialValuation.pen9AverageSalary_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:33:16.790748+00:00
-- url     : https://prove2.me/theorems/f3bb6523-5541-4fe7-838f-c54665bf6758
-- title:
--   Salary scales, average pay and fractional service: pen9AverageSalary_zero
-- statement:
--   An empty average salary window has the specified zero convention. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   \bar S_{0}=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AverageSalary

namespace ActuarialValuation

theorem pen9AverageSalary_zero (salary : ℕ → ℝ) (first : ℕ) : pen9AverageSalary salary first 0 = 0 := by sorry

end ActuarialValuation
