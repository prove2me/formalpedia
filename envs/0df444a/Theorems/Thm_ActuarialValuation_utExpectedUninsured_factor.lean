-- Prove2me | Theorems.Thm_ActuarialValuation_utExpectedUninsured_factor
-- name    : ActuarialValuation.utExpectedUninsured_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:07:40.417514+00:00
-- url     : https://prove2.me/theorems/3b542e94-396e-46fc-b685-697abf17f7ee
-- title:
--   Actuarial insurance certainty equivalents and premium indifference: utExpectedUninsured_factor
-- statement:
--   Expected uninsured CARA utility factorises into wealth utility and exponential loss moment. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_utLossMoment
import Definitions.Def_actuarial_utExpectedUninsured

namespace ActuarialValuation

theorem utExpectedUninsured_factor {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (a wealth : ℝ) : utExpectedUninsured p loss a wealth= -Real.exp (-a*wealth)*utLossMoment p loss a := by sorry

end ActuarialValuation
