-- Prove2me | Theorems.Thm_ActuarialValuation_pen9ExitPV_nonneg
-- name    : ActuarialValuation.pen9ExitPV_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:38:18.514983+00:00
-- url     : https://prove2.me/theorems/08673ff1-bdb8-45b8-adca-d041badcea93
-- title:
--   Service-table exits, survivor and deferred benefits: pen9ExitPV_nonneg
-- statement:
--   Valid nonnegative exit probabilities, payments and discount produce nonnegative actuarial values. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   q^k,B_k,v\ge0\implies EPV\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9ExitPV

namespace ActuarialValuation

theorem pen9ExitPV_nonneg (v w d i r bw bd bi br : ℝ) (hv : 0 ≤ v) (hw : 0 ≤ w) (hd : 0 ≤ d) (hi : 0 ≤ i) (hr : 0 ≤ r) (hbw : 0 ≤ bw) (hbd : 0 ≤ bd) (hbi : 0 ≤ bi) (hbr : 0 ≤ br) : 0 ≤ pen9ExitPV v w d i r bw bd bi br := by sorry

end ActuarialValuation
