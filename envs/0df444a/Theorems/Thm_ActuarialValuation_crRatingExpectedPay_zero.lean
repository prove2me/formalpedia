-- Prove2me | Theorems.Thm_ActuarialValuation_crRatingExpectedPay_zero
-- name    : ActuarialValuation.crRatingExpectedPay_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:11:19.302673+00:00
-- url     : https://prove2.me/theorems/afb45dd5-27f9-4a94-a605-8a95dc92e553
-- title:
--   Three-state rating migration and recoverable default claims: crRatingExpectedPay_zero
-- statement:
--   A bond with zero state-contingent benefit has no payout. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \sum_j P_{ij}=1,\quad P_{\text{default,default}}=1
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 451. Robert C. Merton (1974), On the Pricing of Corporate Debt, Journal of Finance 29(2), 449–470, https://doi.org/10.1111/j.1540-6261.1974.tb03058.x; Jarrow, Lando and Turnbull (1997), Markov Model for the Term Structure of Credit Risk Spreads, https://doi.org/10.1093/rfs/10.2.481. Parent topic: Merton-style terminal firm assets, debt/equity limited liability, credit spread and absorbing finite-state rating transition and default-recovery bond cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.1540-6261.1974.tb03058.x

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crRatingExpectedPay

namespace ActuarialValuation

theorem crRatingExpectedPay_zero (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) : crRatingExpectedPay P i (fun _ => 0)=0 := by sorry

end ActuarialValuation
