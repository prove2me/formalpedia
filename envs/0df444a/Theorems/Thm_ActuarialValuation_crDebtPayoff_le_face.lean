-- Prove2me | Theorems.Thm_ActuarialValuation_crDebtPayoff_le_face
-- name    : ActuarialValuation.crDebtPayoff_le_face
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:04:37.369214+00:00
-- url     : https://prove2.me/theorems/dcbaacaa-1eb8-47d0-a9c8-5facb8cf119a
-- title:
--   Merton limited liability and terminal default payoffs: crDebtPayoff_le_face
-- statement:
--   Bondholders cannot receive above their contractual face value. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem crDebtPayoff_le_face (assets debt : ℝ) : crDebtPayoff assets debt≤debt := by sorry

end ActuarialValuation
