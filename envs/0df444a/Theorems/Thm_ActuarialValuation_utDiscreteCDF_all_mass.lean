-- Prove2me | Theorems.Thm_ActuarialValuation_utDiscreteCDF_all_mass
-- name    : ActuarialValuation.utDiscreteCDF_all_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:09:35.78172+00:00
-- url     : https://prove2.me/theorems/b68541bb-b42f-4e47-a1f2-41e3f83c754c
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utDiscreteCDF_all_mass
-- statement:
--   A threshold exceeding every scenario captures all probability mass. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_utDiscreteCDF

namespace ActuarialValuation

theorem utDiscreteCDF_all_mass {n : ℕ} (p : Fin n → ℝ) (x : Fin n → ℝ) (t : ℝ) (h : ∀ k, x k≤t) (hp : (∑ k : Fin n, p k)=1) : utDiscreteCDF p x t=1 := by sorry

end ActuarialValuation
