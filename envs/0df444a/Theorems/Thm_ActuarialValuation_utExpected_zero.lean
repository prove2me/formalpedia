-- Prove2me | Theorems.Thm_ActuarialValuation_utExpected_zero
-- name    : ActuarialValuation.utExpected_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-10T19:04:13.039061+00:00
-- url     : https://prove2.me/theorems/189bb360-96fd-4d46-873c-4e0fad98d3fc
-- title:
--   Expected exponential utility and absolute risk aversion: utExpected_zero
-- statement:
--   A zero stochastic cashflow has zero expectation. This original derived actuarial relation uses the parameter restrictions, endpoints and units stated in the separate formal theorem or definition.
--
--   Mathematical relation:
--
--   $$
--   u_a(w)=-e^{-aw},\quad A(w)=-u''_a(w)/u'_a(w)=a
--   $$
-- source:
--   Original derived actuarial mathematics, published source page 122. J. W. Pratt, Risk Aversion in the Small and in the Large, Econometrica (1964), https://doi.org/10.2307/1913738; Rothschild and Stiglitz, Increasing Risk I (1970), https://doi.org/10.1016/0022-0531(70)90038-4. Parent topic: CARA utility, Arrow-Pratt aversion, finite-scenario expected insurance utility, exact entropic premium indifference and monotone coupling risk orders. The particular Lean formula is a new finite/real-algebraic formalisation and remains an unproved theorem target if labelled theorem. Relevant published actuarial derivation: https://doi.org/10.2307/1913738

import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Definitions.Def_actuarial_utExpected

namespace ActuarialValuation

theorem utExpected_zero {n : ℕ} (p : Fin n → ℝ) : utExpected p (fun _ => 0)=0 := by sorry

end ActuarialValuation
