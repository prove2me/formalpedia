-- Prove2me | Theorems.Thm_ActuarialValuation_frFractionalValuation_fundamental
-- name    : ActuarialValuation.frFractionalValuation_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T10:26:01.080633+00:00
-- url     : https://prove2.me/theorems/1577db68-c37f-47e1-b1d7-e95be0dfa0ea
-- title:
--   Fractional premiums and policy reserves: frFractionalValuation_fundamental
-- statement:
--   The capstone jointly reconciles annual and single-instalment due valuation, the fractional equivalence premium and the exact survivor reserve balance while preserving constant-force positivity separately from UDD.
--
--   Mathematical relation:
--
--   $$
--   frFractionalValuation\_fundamental
--   $$
--   Original derived theorem target; the Lean statement gives the exact conditions and result.
-- source:
--   Original derived actuarial mathematics inspired by Promislow (2015), chapters 7, 4 and 8, published book reference https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting published actuarial reference https://www.soa.org/498941/globalassets/assets/files/e-business/pd/events/2018/las/pd-2018-05-las-session-033.pdf. Published source page 98 of Promislow's 2015 edition provides the thematic mathematical context. The target Lean identity is an original derivation, not a verbatim published result.

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_actuarial_frDueValue
import Definitions.Def_actuarial_frAnnualDueValue
import Definitions.Def_actuarial_frPremiumPV
import Definitions.Def_actuarial_frNetPremium
import Definitions.Def_actuarial_frFractionalReserve
import Definitions.Def_actuarial_frUddSurvival
import Definitions.Def_actuarial_frForceSurvival

namespace ActuarialValuation

theorem frFractionalValuation_fundamental (c : ℕ → ℝ) (discount : ℝ → ℝ) (p qSeries : ℕ → ℝ) (n : ℕ) (benefitPV annuityPV assets premium benefit q s growth endDiscount mu : ℝ) (ha : annuityPV ≠ 0) (hs : frUddSurvival q s ≠ 0) : (frDueValue c discount p qSeries n 1 = frAnnualDueValue c discount p n) ∧ (frPremiumPV (frNetPremium benefitPV annuityPV) annuityPV = benefitPV) ∧ (frFractionalReserve assets premium benefit q s growth endDiscount * frUddSurvival q s + s*q*benefit*endDiscount = (assets+premium)*growth) ∧ (0 < frForceSurvival mu s) := by sorry

end ActuarialValuation
