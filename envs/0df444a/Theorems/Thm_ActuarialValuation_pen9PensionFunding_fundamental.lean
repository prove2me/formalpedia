-- Prove2me | Theorems.Thm_ActuarialValuation_pen9PensionFunding_fundamental
-- name    : ActuarialValuation.pen9PensionFunding_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T11:42:33.334838+00:00
-- url     : https://prove2.me/theorems/40a80617-34ea-4e27-9d90-6acf5afde4cd
-- title:
--   Projected versus traditional unit credit and reserve recursion: pen9PensionFunding_fundamental
-- statement:
--   A combined pension valuation and funding theorem: DC accumulation finances a salary-replacement pension including survivor annuity; DB projected service cost adds to PUC liability; the TUC difference is the projected salary revaluation; and the annual contribution uniquely balances exit benefits with the continuation reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   A(c^*)=K,\quad AL^{PUC}_{n+1}=AL^{PUC}_n+NC,\quad AL^{PUC}-AL^{TUC}=\alpha n\Delta S f,\quad V_t+C_t=E_t+vp^aV_{t+1}
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 290. Dickson, Hardy and Waters, Actuarial Mathematics for Life Contingent Risks, Chapter 9, Pension Mathematics (2009), https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A; IFRS Foundation, IAS 19 Employee Benefits, paragraphs 67–74, https://www.ifrs.org/issued-standards/list-of-standards/ias-19-employee-benefits/; Actuarial Standards Board, Unit Credit Actuarial Cost Method, https://www.actuarialstandardsboard.org/glossary/unit-credit-actuarial-cost-method/. Parent topic: Pension mathematics: salary-scale and final-average benefit accrual, replacement-ratio DC targets, withdrawal/death/service contingent EPVs, PUC versus TUC, and reserve financing. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.cambridge.org/core/books/abs/actuarial-mathematics-for-life-contingent-risks/pension-mathematics/E935265B9EFB465A282DE1BD6254B67A

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pen9AccumFactor
import Definitions.Def_actuarial_pen9DCFund
import Definitions.Def_actuarial_pen9ReversionaryAnnuity
import Definitions.Def_actuarial_pen9TargetCapital
import Definitions.Def_actuarial_pen9RequiredDCRate
import Definitions.Def_actuarial_pen9PUC
import Definitions.Def_actuarial_pen9TUC
import Definitions.Def_actuarial_pen9PUCNormalCost
import Definitions.Def_actuarial_pen9RequiredContribution
import Definitions.Def_actuarial_pen9ExitPV
import Definitions.Def_actuarial_pen9ActiveProbability

namespace ActuarialValuation

theorem pen9PensionFunding_fundamental (salary : ℕ → ℝ) (investment : ℝ) (years service : ℕ) (retSalary replacement member spouse reversion accrual currentSalary projectedSalary pensionFactor : ℝ) (reserve discount w d i r bw bd bi br nextReserve : ℝ) (hF : pen9AccumFactor salary investment years ≠ 0) : (pen9DCFund (pen9RequiredDCRate (pen9TargetCapital retSalary replacement (pen9ReversionaryAnnuity member spouse reversion)) (pen9AccumFactor salary investment years)) salary investment years = pen9TargetCapital retSalary replacement (pen9ReversionaryAnnuity member spouse reversion)) ∧ (pen9PUC accrual projectedSalary pensionFactor (service+1) = pen9PUC accrual projectedSalary pensionFactor service + pen9PUCNormalCost accrual projectedSalary pensionFactor) ∧ (pen9PUC accrual projectedSalary pensionFactor service - pen9TUC accrual currentSalary pensionFactor service = accrual*(service:ℝ)*(projectedSalary-currentSalary)*pensionFactor) ∧ (reserve + pen9RequiredContribution reserve (pen9ExitPV discount w d i r bw bd bi br) (discount*pen9ActiveProbability w d i r) nextReserve = pen9ExitPV discount w d i r bw bd bi br + (discount*pen9ActiveProbability w d i r)*nextReserve) := by sorry

end ActuarialValuation
