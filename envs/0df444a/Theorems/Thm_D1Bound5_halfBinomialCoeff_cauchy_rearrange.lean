-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_cauchy_rearrange
-- name    : D1Bound5.halfBinomialCoeff_cauchy_rearrange
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:11.340705+00:00
-- url     : https://prove2.me/theorems/d1cce148-c78c-4ec3-aca8-c930f7bd0ed4
-- title:
--   Half Binomial Coeff cauchy rearrange
-- statement:
--   Reassociation of the Cauchy coefficients into genuine homogeneous polynomial coefficients, using only the antidiagonal degree equation.
-- source:
--   D1Bound5/HalfBinomialAnalytic.lean, lines 37-57, SHA-256 109e12b103be56576f2b508ea1bde2f80f1c2a5c9319f282768950102447591a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
namespace D1Bound5






theorem _root_.D1Bound5.halfBinomialCoeff_cauchy_rearrange (x y z : ℂ) (n : ℕ) :
    (∑ ij ∈ Finset.antidiagonal n,
      ((halfBinomialCoeff ij.1 : ℂ) * (x * z) ^ ij.1) *
        ((halfBinomialCoeff ij.2 : ℂ) * (y * z) ^ ij.2)) =
    (∑ ij ∈ Finset.antidiagonal n,
      ((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
        x ^ ij.1 * y ^ ij.2) * z ^ n := by sorry



end D1Bound5
end
