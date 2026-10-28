-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_interior_convolution
-- name    : D1Bound5.halfBinomialCoeff_interior_convolution
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:11.653379+00:00
-- url     : https://prove2.me/theorems/01801c74-d095-4b5c-8ec9-299690752b4b
-- title:
--   Half Binomial Coeff interior convolution
-- statement:
--   The interior coefficients of the half-binomial convolution sum to twice the negative endpoint coefficient.
-- source:
--   D1Bound5/HalfBinomialConvolutionAbs.lean, lines 7-20, SHA-256 1173ab778ae4d08a2f4654331009133181881091b647e271ed67fd57519e3d85. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.halfBinomialCoeff_interior_convolution (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
      halfBinomialCoeff (ij.1 + 1) * halfBinomialCoeff (ij.2 + 1)) =
      -2 * halfBinomialCoeff (k + 2) := by sorry









end D1Bound5
end
