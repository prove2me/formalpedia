-- Prove2me | Theorems.Thm_D1Bound5_first_pair_retained_scalar
-- name    : D1Bound5.first_pair_retained_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:45:08.708285+00:00
-- url     : https://prove2.me/theorems/44f5e25b-5044-415f-8d53-fa7a4e1c322d
-- title:
--   First pair retained scalar
-- statement:
--   The retained interpolation coefficient and the coupled geometry bound yield the three lower estimates used by the S≥15 window chain.
-- source:
--   D1Bound5/FirstPairRetainedScalar.lean, lines 5-86, SHA-256 cb15769d873c8204aa14b74f7f9a3ec39724b76ca98c1d6bf3698917708a54b5. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Util.CollectAxioms
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Algebra.CharP.Frobenius
import Mathlib.Algebra.CharP.Two
import Mathlib.Algebra.Group.Int.Units
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Algebra.Squarefree.Basic
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Data.Real.Basic
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.first_pair_retained_scalar (A B S T C R Q F Phi : ℝ)
    (hA : 1 ≤ A) (hB : 0 < B) (hS : 0 < S) (hT : 0 < T)
    (hR : 0 < R) (hRQ : R ≤ Q) (hF : 0 < F) (hPhi : 0 ≤ Phi)
    (hsep : (51051/400000 : ℝ)/B^2 < 1/Q)
    (hfront : (59/20 : ℝ)*A*B*S < T)
    (hgeom : R^2*Phi ≤ F)
    (hret : (9999/100 : ℝ)*A^2*
      (1/R-(51051/400000 : ℝ)/(A^2*B^2))^2*(T^5/S^2) < C) :
    let K := (9999/100 : ℝ)*A^2*(1/Q-(51051/400000 : ℝ)/B^2)^2
    let H := (9999/100 : ℝ)*A^2*(59/20 : ℝ)^5*
      (1-(51051/400000 : ℝ)*Q/B^2)^2
    K*T^5/S^2 < C ∧ K*(59/20 : ℝ)^5*B^5*S^3 < C ∧
      (H/F)*Phi*B^5*S^3 < C := by sorry

end D1Bound5
end
