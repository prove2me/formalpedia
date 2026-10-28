-- Prove2me | Theorems.Thm_D1Bound5_finiteM_rowfactor_scalar
-- name    : D1Bound5.finiteM_rowfactor_scalar
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:25.427996+00:00
-- url     : https://prove2.me/theorems/49581d51-aa1f-4714-be16-8c1a03a46b32
-- title:
--   Finite M rowfactor scalar
-- statement:
--   Uniform row-factor geometry. Only the elementary upper bounds for the three differences enter; no lower separation estimate is assumed.
-- source:
--   D1Bound5/FiniteMResidual.lean, lines 6-35, SHA-256 20b5f3f0240599a870b13dc7bce59f4a645e7c3a3e921eff6e6196205ed5b078. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.CharZero.Infinite
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

section
namespace D1Bound5


theorem _root_.D1Bound5.finiteM_rowfactor_scalar (A B S x y z r : ℝ)
    (hA : 1 ≤ A) (hAB : A ≤ B) (hBS : B ≤ S)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hxB : x ≤ 2*B) (hyS : y ≤ 2*S) (hzS : z ≤ 2*S)
    (hr : r=x*y*z ∨ r=A*z ∨ r=B*y ∨ r=S*x) :
    A*(x*y*z)^4 ≤ 2048*B^4*S^7*r := by sorry



end D1Bound5
end
