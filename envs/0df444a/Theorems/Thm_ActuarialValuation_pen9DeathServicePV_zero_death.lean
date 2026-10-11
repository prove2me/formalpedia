-- Prove2me | Theorems.Thm_ActuarialValuation_pen9DeathServicePV_zero_death
-- name    : ActuarialValuation.pen9DeathServicePV_zero_death
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:38:47.771039+00:00
-- url     : https://prove2.me/theorems/b2412420-c050-40de-8677-ee89a30a9a8f
-- title:
--   Service-table exits, survivor and deferred benefits: pen9DeathServicePV_zero_death
-- statement:
--   No death-event benefit is payable when the relevant death decrement is zero. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   q^d=0\implies PV_d=0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9DeathServicePV

namespace ActuarialValuation

theorem pen9DeathServicePV_zero_death (s cover ann v : ℝ) : pen9DeathServicePV 0 s cover ann v = 0 := by sorry

end ActuarialValuation
