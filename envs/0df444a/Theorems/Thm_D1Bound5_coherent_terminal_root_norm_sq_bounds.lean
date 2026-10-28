-- Prove2me | Theorems.Thm_D1Bound5_coherent_terminal_root_norm_sq_bounds
-- name    : D1Bound5.coherent_terminal_root_norm_sq_bounds
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:39:08.303593+00:00
-- url     : https://prove2.me/theorems/ebe48180-8676-43ef-b525-6571b40cd83f
-- title:
--   Coherent terminal root norm sq bounds
-- statement:
--   The exact chosen terminal root supplies both modulus-square estimates used by the retained scalar conversion.
-- source:
--   D1Bound5/CoherentRetainedAnalyticData.lean, lines 41-59, SHA-256 e4a665d10b2869f821502c2c77658404842057b13044350eb4f7b226404c0728. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_CoherentIntegralForms_Definitions

section
open Finset

namespace D1Bound5




theorem _root_.D1Bound5.coherent_terminal_root_norm_sq_bounds
    (p q eta : ℂ) (hp : p ≠ 0) (hq : q ≠ 0) (heta : eta^2=p*q)
    (hPQ : 4000 < ‖p‖*‖q‖) :
    (3999/4000 : ℝ)*‖p‖*‖q‖ < ‖coherentTerminalRoot p q eta‖^2 ∧
      ‖coherentTerminalRoot p q eta‖^2 ≤ ‖p‖*‖q‖+1 := by sorry

end D1Bound5
end
