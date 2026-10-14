-- Prove2me | Theorems.Thm_ActuarialValuation_utLossMoment_zero
-- name    : ActuarialValuation.utLossMoment_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:06:10.905584+00:00
-- url     : https://prove2.me/theorems/ca314357-6d75-4224-a644-b5c57c010e91
-- title:
--   Actuarial insurance certainty equivalents and premium indifference: utLossMoment_zero
-- statement:
--   At zero risk aversion the exponential moment is one. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

namespace ActuarialValuation

theorem utLossMoment_zero {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (hp : (∑ k : Fin n, p k)=1) : utLossMoment p loss 0=1 := by sorry

end ActuarialValuation
