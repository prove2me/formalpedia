-- Prove2me | Theorems.Thm_ActuarialValuation_pen9RequiredDCRate_unique
-- name    : ActuarialValuation.pen9RequiredDCRate_unique
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:36:18.817248+00:00
-- url     : https://prove2.me/theorems/d7a094b0-f502-48d5-ace1-dac97a5314d3
-- title:
--   DC accumulation and replacement-ratio annuity funding: pen9RequiredDCRate_unique
-- statement:
--   The salary-proportional funding rate is unique when accumulated payroll is nonzero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   cF=K\implies c=c^*
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9RequiredDCRate

namespace ActuarialValuation

theorem pen9RequiredDCRate_unique (capital factor rate : ℝ) (hf : factor ≠ 0) (h : rate*factor=capital) : rate = pen9RequiredDCRate capital factor := by sorry

end ActuarialValuation
