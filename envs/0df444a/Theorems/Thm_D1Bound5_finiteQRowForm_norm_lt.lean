-- Prove2me | Theorems.Thm_D1Bound5_finiteQRowForm_norm_lt
-- name    : D1Bound5.finiteQRowForm_norm_lt
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:15.182242+00:00
-- url     : https://prove2.me/theorems/0cbf905b-334d-45c0-87d5-bbe823d1b424
-- title:
--   Finite QRow Form norm lt
-- statement:
--   The actual Q row has coefficient54 after the signed-root transfer. Only the root error estimates are intermediate hypotheses here; its height and residual estimates are derived from the constructed family.
-- source:
--   D1Bound5/FiniteQRowBound.lean, lines 52-83, SHA-256 791fbd5ab0485888fc2207407e4522dac5c3ad388f70c392e5ef0228d0e3578f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Int.GCD
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_FiniteQIntegralRows_Definitions
import Definitions.Def_D1Bound5_FiniteQRowBound_Definitions

section
namespace D1Bound5










theorem _root_.D1Bound5.finiteQRowForm_norm_lt
    (a b s t c z rA rB rS rT : ℂ) (A T : ℝ) (hA : 0 < A) (hz : z ≠ 0)
    (hlower : ∀ j, A ≤ ‖finiteQAnchors a b s t j‖)
    (hupper : ∀ j, ‖finiteQAnchors a b s t j‖ ≤ T)
    (hAC : 1000 ≤ A*‖c‖)
    (herr : ∀ j : Fin 4,
      ‖((1+1/(finiteQAnchors a b s t j*c))^(1/2 : ℂ)) -
        ![rA,rB,rS,rT] j/(finiteQAnchors a b s t j*z)‖ ≤
          (3/2 : ℝ)*‖c‖/(‖finiteQAnchors a b s t j‖*‖z‖^2)) (i : Fin 5) :
    ‖finiteQRowForm a b s t c z rA rB rS rT i‖ <
      54*T^3*‖c‖^2/‖z‖+3*T*‖z‖/(2*A^2*‖c‖^4) := by sorry

end D1Bound5
end
