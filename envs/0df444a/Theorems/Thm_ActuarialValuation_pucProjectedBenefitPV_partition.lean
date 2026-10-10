-- Prove2me | Theorems.Thm_ActuarialValuation_pucProjectedBenefitPV_partition
-- name    : ActuarialValuation.pucProjectedBenefitPV_partition
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:06:39.260963+00:00
-- url     : https://prove2.me/theorems/3e18aa88-7665-4d2e-89a3-b623b90ac5fb
-- title:
--   Actuarial liability and normal cost: pucProjectedBenefitPV_partition
-- statement:
--   Total projected pension value partitions exactly between past service liability and cost attributed to future service. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   PVFB=AL+PVFNC
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 5. American Academy of Actuaries, Fundamentals of Pension Accounting and Funding (2004), https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf; IFoA GN26 Pension Fund Terminology (2006), https://www.actuaries.org.uk/system/files/documents/pdf/gn26v2-1.pdf; IMF, Conducting Stress Tests of Defined Benefit Pension Plans (2014), https://www.elibrary.imf.org/display/book/9781484368589/ch012.xml. Parent topic: Projected unit credit pension funding, service attribution, normal cost, actuarial liability and amortisation of unfunded pension liabilities. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://www.actuary.org/sites/default/files/pdf/pension/fundamentals_0704.pdf

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_pucActuarialLiability
import Definitions.Def_actuarial_pucFutureNormalCost
import Definitions.Def_actuarial_pucProjectedBenefitPV

namespace ActuarialValuation

theorem pucProjectedBenefitPV_partition (u : ℕ → ℝ) (n m : ℕ) (f : ℝ) : pucProjectedBenefitPV u n m f = pucActuarialLiability u n f + pucFutureNormalCost u n m f := by sorry

end ActuarialValuation
