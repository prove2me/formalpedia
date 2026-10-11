-- Prove2me | Theorems.Thm_ActuarialValuation_crDefault_iff
-- name    : ActuarialValuation.crDefault_iff
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:06:00.448103+00:00
-- url     : https://prove2.me/theorems/f4098576-fc5e-4a73-98b3-3ca35379e99d
-- title:
--   Merton limited liability and terminal default payoffs: crDefault_iff
-- statement:
--   Strict asset deficit is equivalent to zero equity except for solvent zero-cashflow special cases. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crDefault

namespace ActuarialValuation

theorem crDefault_iff (assets debt : ℝ) : crDefault assets debt ↔ crEquityPayoff assets debt=0 ∧ assets≠debt := by sorry

end ActuarialValuation
