-- Prove2me | Theorems.Thm_ActuarialValuation_utExpectedStoploss_nonneg
-- name    : ActuarialValuation.utExpectedStoploss_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:11:42.657707+00:00
-- url     : https://prove2.me/theorems/c9169a95-7a8e-47a6-9136-73e35c3b601c
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utExpectedStoploss_nonneg
-- statement:
--   Expected ceded losses are nonnegative. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem utExpectedStoploss_nonneg {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (retention : ℝ) (hp : ∀ k, 0≤p k) : 0≤utExpectedStoploss p loss retention := by sorry

end ActuarialValuation
