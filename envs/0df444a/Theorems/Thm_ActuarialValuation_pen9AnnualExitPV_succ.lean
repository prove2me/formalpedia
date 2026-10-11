-- Prove2me | Theorems.Thm_ActuarialValuation_pen9AnnualExitPV_succ
-- name    : ActuarialValuation.pen9AnnualExitPV_succ
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T11:39:19.011088+00:00
-- url     : https://prove2.me/theorems/6691135d-8907-4f22-ba5c-bb96b336819c
-- title:
--   Service-table exits, survivor and deferred benefits: pen9AnnualExitPV_succ
-- statement:
--   Adding one exit year adds exactly its probability-weighted payment. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   EPV_{n+1}=EPV_n+p_nv_nB_n
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AnnualExitPV

namespace ActuarialValuation

theorem pen9AnnualExitPV_succ (p v b : ℕ → ℝ) (n : ℕ) : pen9AnnualExitPV p v b (n+1) = pen9AnnualExitPV p v b n + p n*v n*b n := by sorry

end ActuarialValuation
