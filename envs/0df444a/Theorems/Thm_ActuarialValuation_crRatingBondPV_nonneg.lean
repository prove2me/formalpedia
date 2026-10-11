-- Prove2me | Theorems.Thm_ActuarialValuation_crRatingBondPV_nonneg
-- name    : ActuarialValuation.crRatingBondPV_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:12:04.319105+00:00
-- url     : https://prove2.me/theorems/769f30ee-3995-40a7-b2bc-426fa671bd78
-- title:
--   Three-state rating migration and recoverable default claims: crRatingBondPV_nonneg
-- statement:
--   Expected discounted recovery is nonnegative under a proper rating law. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crRatingBondPV

namespace ActuarialValuation

theorem crRatingBondPV_nonneg (P : Fin 3 → Fin 3 → ℝ) (i : Fin 3) (cash : Fin 3 → ℝ) (discount : ℝ) (hP : ∀ j, 0≤P i j) (hc : ∀ j, 0≤cash j) (hd : 0≤discount) : 0≤crRatingBondPV P i cash discount := by sorry

end ActuarialValuation
