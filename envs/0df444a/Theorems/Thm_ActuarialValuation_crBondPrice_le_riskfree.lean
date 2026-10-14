-- Prove2me | Theorems.Thm_ActuarialValuation_crBondPrice_le_riskfree
-- name    : ActuarialValuation.crBondPrice_le_riskfree
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:07:54.995982+00:00
-- url     : https://prove2.me/theorems/66fde805-1943-4413-ae4c-733393bfeb42
-- title:
--   Finite default risk premiums and risk-neutral debt pricing: crBondPrice_le_riskfree
-- statement:
--   Defaultable corporate bond is no dearer than identical risk-free promise. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_crBondPrice
import Definitions.Def_actuarial_crRiskfreeBond

namespace ActuarialValuation

theorem crBondPrice_le_riskfree {m : ℕ} (p : Fin m → ℝ) (assets : Fin m → ℝ) (debt discount : ℝ) (hp : ∀ i, 0≤p i) (hn : (∑ i : Fin m, p i)=1) (hdisc : 0≤discount) : crBondPrice p assets debt discount≤crRiskfreeBond debt discount := by sorry

end ActuarialValuation
