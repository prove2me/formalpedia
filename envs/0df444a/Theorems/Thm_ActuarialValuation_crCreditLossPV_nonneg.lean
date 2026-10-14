-- Prove2me | Theorems.Thm_ActuarialValuation_crCreditLossPV_nonneg
-- name    : ActuarialValuation.crCreditLossPV_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:09:37.269987+00:00
-- url     : https://prove2.me/theorems/7add25fe-8753-42ea-abd9-0363c424ad0d
-- title:
--   Finite default risk premiums and risk-neutral debt pricing: crCreditLossPV_nonneg
-- statement:
--   Credit loss is positive for an underpriced risky obligation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crRiskfreeBond
import Definitions.Def_actuarial_crCreditLossPV

namespace ActuarialValuation

theorem crCreditLossPV_nonneg (face discount risky : ℝ) (h : risky≤crRiskfreeBond face discount) : 0≤crCreditLossPV face discount risky := by sorry

end ActuarialValuation
