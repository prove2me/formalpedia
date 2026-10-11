-- Prove2me | Theorems.Thm_ActuarialValuation_utRiskLoading_nonneg
-- name    : ActuarialValuation.utRiskLoading_nonneg
-- status  : Open
-- author  : @WillR
-- created : 2026-10-10T19:08:52.366417+00:00
-- url     : https://prove2.me/theorems/bd03bc3e-f20f-4d43-bd7e-85e76c5a49b2
-- title:
--   Actuarial insurance certainty equivalents and premium indifference: utRiskLoading_nonneg
-- statement:
--   Risk-averse exponential expected utility demands at least the expected claim cost. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   \pi_a(X)=\frac{1}{a}\log\mathbb E[e^{aX}]
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 122. J. W. Pratt, Risk Aversion in the Small and in the Large, Econometrica (1964), https://doi.org/10.2307/1913738; Rothschild and Stiglitz, Increasing Risk I (1970), https://doi.org/10.1016/0022-0531(70)90038-4. Parent topic: CARA utility, Arrow-Pratt aversion, finite-scenario expected insurance utility, exact entropic premium indifference and monotone coupling risk orders. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/1913738

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utRiskLoading

namespace ActuarialValuation

theorem utRiskLoading_nonneg {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (a : ℝ) (ha : 0<a) (hp : ∀ k, 0≤p k) (hn : (∑ k : Fin n, p k)=1) : 0≤utRiskLoading p loss a := by sorry

end ActuarialValuation
