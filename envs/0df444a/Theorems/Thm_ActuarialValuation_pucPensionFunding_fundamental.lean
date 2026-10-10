-- Prove2me | Theorems.Thm_ActuarialValuation_pucPensionFunding_fundamental
-- name    : ActuarialValuation.pucPensionFunding_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:15:33.760158+00:00
-- url     : https://prove2.me/theorems/d18fa93b-b643-4e16-98cd-6ed071e1a503
-- title:
--   Funding shortfall and contribution amortisation: pucPensionFunding_fundamental
-- statement:
--   The pension funding capstone unites projected-unit service attribution with the exact amortisation contribution threshold and surplus monotonicity. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PVFB=AL+PVFNC,\quad c^*F=UL,\quad c\ge c^*\Rightarrow S(c)\ge0
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucActuarialLiability
import Definitions.Def_actuarial_pucFutureNormalCost
import Definitions.Def_actuarial_pucProjectedBenefitPV
import Definitions.Def_actuarial_pucUnfundedLiability
import Definitions.Def_actuarial_pucAmortisationRate
import Definitions.Def_actuarial_pucFundingSurplus

namespace ActuarialValuation

theorem pucPensionFunding_fundamental (unit : ℕ → ℝ) (n m : ℕ) (f assets payrollPV : ℝ) (hF : 0 < payrollPV) (hUL : 0 ≤ pucUnfundedLiability (pucActuarialLiability unit n f) assets) : (pucProjectedBenefitPV unit n m f = pucActuarialLiability unit n f + pucFutureNormalCost unit n m f) ∧ (0 ≤ pucAmortisationRate (pucUnfundedLiability (pucActuarialLiability unit n f) assets) payrollPV) ∧ (pucFundingSurplus assets (pucAmortisationRate (pucUnfundedLiability (pucActuarialLiability unit n f) assets) payrollPV) payrollPV (pucActuarialLiability unit n f) = 0) ∧ (∀ c : ℝ, pucAmortisationRate (pucUnfundedLiability (pucActuarialLiability unit n f) assets) payrollPV ≤ c → 0 ≤ pucFundingSurplus assets c payrollPV (pucActuarialLiability unit n f)) := by sorry

end ActuarialValuation
