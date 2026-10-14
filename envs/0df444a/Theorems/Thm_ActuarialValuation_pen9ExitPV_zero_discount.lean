-- Prove2me | Theorems.Thm_ActuarialValuation_pen9ExitPV_zero_discount
-- name    : ActuarialValuation.pen9ExitPV_zero_discount
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:37:57.335041+00:00
-- url     : https://prove2.me/theorems/7ff818ab-6541-40dc-8e1d-2528cac8e240
-- title:
--   Service-table exits, survivor and deferred benefits: pen9ExitPV_zero_discount
-- statement:
--   Zero discount value eliminates the present value of service exits. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   v=0\implies EPV=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitPV

namespace ActuarialValuation

theorem pen9ExitPV_zero_discount (w d i r bw bd bi br : ℝ) : pen9ExitPV 0 w d i r bw bd bi br = 0 := by sorry

end ActuarialValuation
