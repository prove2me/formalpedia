-- Prove2me | Theorems.Thm_ActuarialValuation_crEquityPayoff_nonneg
-- name    : ActuarialValuation.crEquityPayoff_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:03:06.984913+00:00
-- url     : https://prove2.me/theorems/eacec11e-93d9-4153-a46d-c5ef7d51b916
-- title:
--   Merton limited liability and terminal default payoffs: crEquityPayoff_nonneg
-- statement:
--   Limited liability prevents negative shareholder wealth. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   E_T=(V_T-D)^+,\quad B_T=\min(V_T,D)
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 451. Robert C. Merton (1974), On the Pricing of Corporate Debt, Journal of Finance 29(2), 449–470, https://doi.org/10.1111/j.1540-6261.1974.tb03058.x; Jarrow, Lando and Turnbull (1997), Markov Model for the Term Structure of Credit Risk Spreads, https://doi.org/10.1093/rfs/10.2.481. Parent topic: Merton-style terminal firm assets, debt/equity limited liability, credit spread and absorbing finite-state rating transition and default-recovery bond cashflows. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.1111/j.1540-6261.1974.tb03058.x

import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_crEquityPayoff

namespace ActuarialValuation

theorem crEquityPayoff_nonneg (assets debt : ℝ) : 0≤crEquityPayoff assets debt := by sorry

end ActuarialValuation
