-- Prove2me | Theorems.Thm_ActuarialValuation_crCreditSpread_nonneg
-- name    : ActuarialValuation.crCreditSpread_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:09:50.413194+00:00
-- url     : https://prove2.me/theorems/1d3523fd-5a6d-4cc9-ba3b-ae81801cfaa7
-- title:
--   Finite default risk premiums and risk-neutral debt pricing: crCreditSpread_nonneg
-- statement:
--   A weaker price for defaultable debt implies a larger compounded yield. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   B_0=e^{-rT}\mathbb E^{\mathbb Q}[\min(V_T,D)]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 451. Robert C. Merton (1974), On the Pricing of Corporate Debt, Journal of Finance 29(2), 449–470, https://doi.org/10.1111/j.1540-6261.1974.tb03058.x; Jarrow, Lando and Turnbull (1997), Markov Model for the Term Structure of Credit Risk Spreads, https://doi.org/10.1093/rfs/10.2.481. Parent topic: Merton-style terminal firm assets, debt/equity limited liability, credit spread and absorbing finite-state rating transition and default-recovery bond cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.1540-6261.1974.tb03058.x

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crCreditSpread

namespace ActuarialValuation

theorem crCreditSpread_nonneg (face riskfree risky term : ℝ) (hface : 0<face) (hriskfree : 0<riskfree) (hrisky : 0<risky) (hterm : 0<term) (h : risky≤riskfree) : 0≤crCreditSpread face riskfree risky term := by sorry

end ActuarialValuation
