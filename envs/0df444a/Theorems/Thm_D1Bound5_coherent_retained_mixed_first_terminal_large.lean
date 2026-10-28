-- Prove2me | Theorems.Thm_D1Bound5_coherent_retained_mixed_first_terminal_large
-- name    : D1Bound5.coherent_retained_mixed_first_terminal_large
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:30.527299+00:00
-- url     : https://prove2.me/theorems/de33aa9f-1be0-4afc-b845-9e43db1f4ed1
-- title:
--   Coherent retained mixed first terminal large
-- statement:
--   The first retained power gap separates the fourth anchor from the first terminal by the factor needed in the direct-four estimate.
-- source:
--   D1Bound5/CoherentRetainedMixedFourSizes.lean, lines 5-36, SHA-256 bf8b694974926c3ebaa1cf7f2ccd931cddc284428c831b170580e4446c6fde48. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.coherent_retained_mixed_first_terminal_large
    (A B S T C : ℝ) (hA : 1 ≤ A) (hB : 3 ≤ B) (hS : 0 < S)
    (hBS : B ≤ S) (hST : S ≤ T)
    (hfront : 2*A*B*S < T) (hgap : A^2*T^5/S^2 < C) :
    16*B*S*T < C := by sorry





end D1Bound5
end
