-- Prove2me | Theorems.Thm_ActuarialValuation_pen9MidSalary_symm
-- name    : ActuarialValuation.pen9MidSalary_symm
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:32:52.196987+00:00
-- url     : https://prove2.me/theorems/c7a576a3-0bf2-4d35-8e83-51eea2cdc9fd
-- title:
--   Salary scales, average pay and fractional service: pen9MidSalary_symm
-- statement:
--   A midpoint interpolation is symmetric in its endpoint salaries. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   S_{1/2}(a,b)=S_{1/2}(b,a)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9MidSalary

namespace ActuarialValuation

theorem pen9MidSalary_symm (a b : ℝ) : pen9MidSalary a b = pen9MidSalary b a := by sorry

end ActuarialValuation
