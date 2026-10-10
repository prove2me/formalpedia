-- Prove2me | Theorems.Thm_ActuarialValuation_alterationReservePaidUpSurrender_fundamental
-- name    : ActuarialValuation.alterationReservePaidUpSurrender_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T06:15:39.932331+00:00
-- url     : https://prove2.me/theorems/21a2089e-f753-48c4-92f5-71edba9128a7
-- title:
--   Surrender deductions and policy value comparisons: alterationReservePaidUpSurrender_fundamental
-- statement:
--   Main policy alteration theorem reconciles prospective reserve, repriced premium difference and reserve-equivalent paid-up cover while bounding surrender cash by the reserve. The full Lean declaration specifies the finite boundaries, exact units and any positivity, independence or regularity assumptions. This is an original derived Actuarial mathematical statement, not a claim of a numbered previously published theorem.
--
--   Mathematical relation:
--
--   $$
--   V=(P_s-P)a=b_{\rm PU}A_{\rm unit},\quad0\le SV\le V
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 90. S. David Promislow, Fundamentals of Actuarial Mathematics (2010/2015), Chapter 6, Section 6.8, Premium difference and paid-up formulas, https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6; Dickson Hardy Waters (2009), Actuarial Mathematics for Life Contingent Risks, policy values, https://www.cambridge.org/core/books/actuarial-mathematics-for-life-contingent-risks/51C0B04099D4DE1D1DDEF9551024133B/listing. Parent topic: Prospective life insurance policy reserves, premium differences, paid-up insurance amounts and surrender values. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://onlinelibrary.wiley.com/doi/10.1002/9781119971528.ch6

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Definitions.Def_actuarial_alterationProspectiveReserve
import Definitions.Def_actuarial_alterationRepricedPremium
import Definitions.Def_actuarial_alterationPremiumDifference
import Definitions.Def_actuarial_alterationPaidUpBenefit
import Definitions.Def_actuarial_alterationPaidUpValue
import Definitions.Def_actuarial_alterationSurrenderValue

namespace ActuarialValuation

theorem alterationReservePaidUpSurrender_fundamental (B A P unitPV deduction : ℝ) (hA : A ≠ 0) (hu : 0 < unitPV) (hV : 0 ≤ alterationProspectiveReserve B A P) (hd : 0 ≤ deduction) (hle : deduction ≤ alterationProspectiveReserve B A P) : (alterationPremiumDifference (alterationRepricedPremium B A) P A = alterationProspectiveReserve B A P) ∧ (alterationPaidUpValue (alterationPaidUpBenefit (alterationProspectiveReserve B A P) unitPV) unitPV = alterationProspectiveReserve B A P) ∧ (0 ≤ alterationSurrenderValue (alterationProspectiveReserve B A P) deduction) ∧ (alterationSurrenderValue (alterationProspectiveReserve B A P) deduction ≤ alterationProspectiveReserve B A P) := by sorry

end ActuarialValuation
