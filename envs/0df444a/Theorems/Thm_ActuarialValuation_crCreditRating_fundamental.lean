-- Prove2me | Theorems.Thm_ActuarialValuation_crCreditRating_fundamental
-- name    : ActuarialValuation.crCreditRating_fundamental
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:13:14.305271+00:00
-- url     : https://prove2.me/theorems/32a406b5-4431-4840-a0a1-688d6264c364
-- title:
--   Three-state rating migration and recoverable default claims: crCreditRating_fundamental
-- statement:
--   Structural terminal solvency and an independent absorbing-rating transition system reconcile riskier defaultable debt prices, nonnegative credit value deductions and genuinely two-period probability conservation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crBondPrice
import Definitions.Def_actuarial_crRiskfreeBond
import Definitions.Def_actuarial_crCreditLossPV
import Definitions.Def_actuarial_crRatingTwoStep

namespace ActuarialValuation

theorem crCreditRating_fundamental {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (face discount : ℝ) (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (hp : ∀ j, 0≤p j) (hn : (∑ j : Fin m, p j)=1) (ha : ∀ j, 0≤assets j) (hf : 0≤face) (hd : 0≤discount) (hP : ∀ j, (∑ k : Fin 3, P j k)=1) : (crBondPrice p assets face discount≤crRiskfreeBond face discount) ∧ ((∑ k : Fin 3, crRatingTwoStep P i k)=1) ∧ (crCreditLossPV face discount (crBondPrice p assets face discount)≥0) := by sorry

end ActuarialValuation
