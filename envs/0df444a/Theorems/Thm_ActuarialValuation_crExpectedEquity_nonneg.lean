-- Prove2me | Theorems.Thm_ActuarialValuation_crExpectedEquity_nonneg
-- name    : ActuarialValuation.crExpectedEquity_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:06:55.231387+00:00
-- url     : https://prove2.me/theorems/cb88c21b-a900-4567-a336-9a0622978aa2
-- title:
--   Finite default risk premiums and risk-neutral debt pricing: crExpectedEquity_nonneg
-- statement:
--   Limited-liability equity remains nonnegative under any nonnegative probability weights. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crExpectedEquity

namespace ActuarialValuation

theorem crExpectedEquity_nonneg {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (debt : ℝ) (hp : ∀ i, 0≤p i) : 0≤crExpectedEquity p assets debt := by sorry

end ActuarialValuation
