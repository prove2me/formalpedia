-- Prove2me | Theorems.Thm_ActuarialValuation_pen9DCFund_add_rates
-- name    : ActuarialValuation.pen9DCFund_add_rates
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:34:50.423862+00:00
-- url     : https://prove2.me/theorems/c29bd819-99a2-4630-b6c6-37ee9bbdab04
-- title:
--   DC accumulation and replacement-ratio annuity funding: pen9DCFund_add_rates
-- statement:
--   Member and employer contributions add linearly when they share investment and timing assumptions. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   A_n(c_1+c_2)=A_n(c_1)+A_n(c_2)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9DCFund

namespace ActuarialValuation

theorem pen9DCFund_add_rates (c₁ c₂ : ℝ) (s : ℕ → ℝ) (j : ℝ) (n : ℕ) : pen9DCFund (c₁+c₂) s j n = pen9DCFund c₁ s j n + pen9DCFund c₂ s j n := by sorry

end ActuarialValuation
