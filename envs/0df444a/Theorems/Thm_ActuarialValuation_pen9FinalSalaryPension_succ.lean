-- Prove2me | Theorems.Thm_ActuarialValuation_pen9FinalSalaryPension_succ
-- name    : ActuarialValuation.pen9FinalSalaryPension_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:33:44.303219+00:00
-- url     : https://prove2.me/theorems/fed05de7-7507-4d37-94de-53161ac664f6
-- title:
--   Salary scales, average pay and fractional service: pen9FinalSalaryPension_succ
-- statement:
--   An additional complete service year credits exactly one extra annual benefit unit. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   B_{n+1}=B_n+\alpha S
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9FinalSalaryPension

namespace ActuarialValuation

theorem pen9FinalSalaryPension_succ (a s : ℝ) (n : ℕ) : pen9FinalSalaryPension a s (n+1) = pen9FinalSalaryPension a s n + a*s := by sorry

end ActuarialValuation
