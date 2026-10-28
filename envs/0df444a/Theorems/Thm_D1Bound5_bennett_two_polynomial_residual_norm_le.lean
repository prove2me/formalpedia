-- Prove2me | Theorems.Thm_D1Bound5_bennett_two_polynomial_residual_norm_le
-- name    : D1Bound5.bennett_two_polynomial_residual_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:52.75077+00:00
-- url     : https://prove2.me/theorems/de3b6215-c58a-4922-99dc-703ac33a3c7a
-- title:
--   Bennett two polynomial residual norm le
-- statement:
--   Exact two-anchor analytic residual estimate, including the manuscript's Gamma factor and exponent 2k-1/2. This concerns the actual P-matrix.
-- source:
--   D1Bound5/BennettResidualBound.lean, lines 60-80, SHA-256 8d3e33dd05c3d6f083c46bb963cedd7bdf12fde7cdfacb5185f8bb3a9a8ff44f. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.bennett_two_polynomial_residual_norm_le
    (a : Fin 3 → ℂ) (ha : Function.Injective a) (k : ℕ) (hk : 1 ≤ k)
    (ρ : ℝ) (x : ℂ) (i : Fin 3)
    (hρ0 : 0 ≤ ρ) (hρ : ∀ j, ‖a j‖ ≤ ρ) (hradius : ρ * ‖x‖ < 1) :
    ‖∑ j, (bennettPolynomialResidue univ a k (1 / 2 : ℂ) i j).eval x *
        (1 + a j * x) ^ (1 / 2 : ℂ)‖ ≤
      (Real.Gamma ((k : ℝ) + 3 / 2) * Real.Gamma (2 * (k : ℝ) - 1 / 2) /
        (Real.pi * Real.Gamma (3 * (k : ℝ) + 1))) * ‖x‖ ^ (3 * k) /
          (1 - ρ * ‖x‖) ^ (2 * (k : ℝ) - 1 / 2) := by sorry

end D1Bound5
end
