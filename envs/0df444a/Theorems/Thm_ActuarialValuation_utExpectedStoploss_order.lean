-- Prove2me | Theorems.Thm_ActuarialValuation_utExpectedStoploss_order
-- name    : ActuarialValuation.utExpectedStoploss_order
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:11:59.042484+00:00
-- url     : https://prove2.me/theorems/9f8831b5-0841-45fb-a675-7757e44dbc42
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utExpectedStoploss_order
-- statement:
--   First-order coupled loss dominance preserves stop-loss premium order. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_utExpectedStoploss

namespace ActuarialValuation

theorem utExpectedStoploss_order {n : ℕ} (p : Fin n → ℝ) (x y : Fin n → ℝ) (retention : ℝ) (hp : ∀ k, 0≤p k) (hxy : ∀ k, x k≤y k) : utExpectedStoploss p x retention≤utExpectedStoploss p y retention := by sorry

end ActuarialValuation
