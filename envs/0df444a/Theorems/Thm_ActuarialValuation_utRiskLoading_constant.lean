-- Prove2me | Theorems.Thm_ActuarialValuation_utRiskLoading_constant
-- name    : ActuarialValuation.utRiskLoading_constant
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:08:19.66704+00:00
-- url     : https://prove2.me/theorems/a7d54caf-6744-4bf9-b4e1-30720800e394
-- title:
--   Actuarial insurance certainty equivalents and premium indifference: utRiskLoading_constant
-- statement:
--   A deterministic insurance claim needs no uncertainty loading. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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

theorem utRiskLoading_constant {n : ℕ} (p : Fin n → ℝ) (a loss : ℝ) (ha : a≠0) (hp : (∑ k : Fin n, p k)=1) : utRiskLoading p (fun _ => loss) a=0 := by sorry

end ActuarialValuation
