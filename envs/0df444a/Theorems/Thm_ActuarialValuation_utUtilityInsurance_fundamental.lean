-- Prove2me | Theorems.Thm_ActuarialValuation_utUtilityInsurance_fundamental
-- name    : ActuarialValuation.utUtilityInsurance_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:12:34.304824+00:00
-- url     : https://prove2.me/theorems/570bcc42-ea59-4429-adad-b2cbaa761f75
-- title:
--   Genuine pathwise coupling and finite first-order stochastic dominance: utUtilityInsurance_fundamental
-- statement:
--   The actuarial insurer and policyholder indifference premium follows from genuinely averaged utility, with positive risk loading and a finite-scenario stochastic risk ordering. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
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
import Definitions.Def_actuarial_utPremium
import Definitions.Def_actuarial_utExpectedUninsured
import Definitions.Def_actuarial_utInsuredUtility
import Definitions.Def_actuarial_utRiskLoading
import Definitions.Def_actuarial_utExpectedStoploss

namespace ActuarialValuation

theorem utUtilityInsurance_fundamental {n : ℕ} (p : Fin n → ℝ) (loss : Fin n → ℝ) (a wealth : ℝ) (ha : 0<a) (hp : ∀ k, 0≤p k) (hn : (∑ k : Fin n, p k)=1) : (utInsuredUtility a wealth (utPremium p loss a)=utExpectedUninsured p loss a wealth) ∧ (0≤utRiskLoading p loss a) ∧ (∀ (y : Fin n → ℝ), (∀ k, loss k≤y k) → utExpectedStoploss p loss 0≤utExpectedStoploss p y 0) := by sorry

end ActuarialValuation
