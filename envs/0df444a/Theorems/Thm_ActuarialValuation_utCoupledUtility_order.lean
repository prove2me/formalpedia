-- Prove2me | Theorems.Thm_ActuarialValuation_utCoupledUtility_order
-- name    : ActuarialValuation.utCoupledUtility_order
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:10:59.45906+00:00
-- url     : https://prove2.me/theorems/d8458eb8-679c-4401-9f7b-cf84c19101ed
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utCoupledUtility_order
-- statement:
--   Increasing CARA utility prefers the dominant scenario-coupled wealth distribution. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   X\le Y\ \text{a.s.}\Longrightarrow \mathbb E[\phi(X)]\le\mathbb E[\phi(Y)]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 122. J. W. Pratt, Risk Aversion in the Small and in the Large, Econometrica (1964), https://doi.org/10.2307/1913738; Rothschild and Stiglitz, Increasing Risk I (1970), https://doi.org/10.1016/0022-0531(70)90038-4. Parent topic: CARA utility, Arrow-Pratt aversion, finite-scenario expected insurance utility, exact entropic premium indifference and monotone coupling risk orders. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/1913738

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utCARA
import Definitions.Def_actuarial_utExpectedUtility

namespace ActuarialValuation

theorem utCoupledUtility_order {n : ℕ} (p : Fin n → ℝ) (x y : Fin n → ℝ) (a : ℝ) (ha : 0<a) (hp : ∀ k, 0≤p k) (hxy : ∀ k, x k≤y k) : utExpectedUtility p x (utCARA a)≤utExpectedUtility p y (utCARA a) := by sorry

end ActuarialValuation
