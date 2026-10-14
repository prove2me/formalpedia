-- Prove2me | Theorems.Thm_ActuarialValuation_crDebtPayoff_nonneg
-- name    : ActuarialValuation.crDebtPayoff_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:04:50.689542+00:00
-- url     : https://prove2.me/theorems/5cc6071e-a845-4d1b-82aa-2ea53585ba62
-- title:
--   Merton limited liability and terminal default payoffs: crDebtPayoff_nonneg
-- statement:
--   Nonnegative assets and face value give nonnegative creditor recovery. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crDebtPayoff

namespace ActuarialValuation

theorem crDebtPayoff_nonneg (assets debt : ℝ) (ha : 0≤assets) (hd : 0≤debt) : 0≤crDebtPayoff assets debt := by sorry

end ActuarialValuation
