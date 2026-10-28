-- Prove2me | Theorems.Thm_D1Bound5_bennettPolynomialResidue_residual_norm_le
-- name    : D1Bound5.bennettPolynomialResidue_residual_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:52.498589+00:00
-- url     : https://prove2.me/theorems/b0a21532-4196-4208-9e47-12a8925b8496
-- title:
--   Bennett Polynomial Residue residual norm le
-- statement:
--   An unconditional analytic bound for the actual arbitrary-order Bennett residual. The proof joins actual polynomial evaluation, exact residue moments, the repeated-node homogeneous identity, and the convergent binomial majorant. No contour formula or residual-bound hypothesis occurs in the statement.
-- source:
--   D1Bound5/BennettResidualBound.lean, lines 10-58, SHA-256 8d3e33dd05c3d6f083c46bb963cedd7bdf12fde7cdfacb5185f8bb3a9a8ff44f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Lean.Elab.Tactic.Omega
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.PartialFractions
import Mathlib.Algebra.Polynomial.Reverse
import Mathlib.Algebra.Polynomial.RingDivision
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Matrix.Polynomial
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.RingTheory.PowerSeries.Trunc
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_BennettResiduePolynomials_Definitions

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.bennettPolynomialResidue_residual_norm_le
    {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℂ) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ν ρ : ℝ) (x : ℂ) (i : I)
    (hs : (k : ℝ) + ν < (Fintype.card I * k : ℕ))
    (hρ0 : 0 ≤ ρ) (hρ : ∀ j, ‖a j‖ ≤ ρ) (hradius : ρ * ‖x‖ < 1) :
    ‖∑ j, (bennettPolynomialResidue univ a k (ν : ℂ) i j).eval x *
        (1 + a j * x) ^ (ν : ℂ)‖ ≤
      |Ring.choose ((k : ℝ) + ν) (Fintype.card I * k)| *
        ‖x‖ ^ (Fintype.card I * k) /
          (1 - ρ * ‖x‖) ^ (((Fintype.card I * k : ℕ) : ℝ) - ((k : ℝ) + ν)) := by sorry



end D1Bound5
end
