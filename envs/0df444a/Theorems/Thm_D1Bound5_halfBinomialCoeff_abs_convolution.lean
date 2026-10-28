-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_convolution
-- name    : D1Bound5.halfBinomialCoeff_abs_convolution
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:37:13.896905+00:00
-- url     : https://prove2.me/theorems/d07053f8-92ae-4a6a-9d2c-5603679968fd
-- title:
--   Half Binomial Coeff abs convolution
-- statement:
--   Sharp absolute half-binomial convolution, valid at every degree >= 2.
-- source:
--   D1Bound5/HalfBinomialConvolutionAbs.lean, lines 70-83, SHA-256 1173ab778ae4d08a2f4654331009133181881091b647e271ed67fd57519e3d85. Project: https://github.com/tomislav-math/d1-bound5-lean

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










theorem _root_.D1Bound5.halfBinomialCoeff_abs_convolution (n : ℕ) (hn : 2 ≤ n) :
    (∑ ij ∈ Finset.antidiagonal n,
      |halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2|) =
        4 * |halfBinomialCoeff n| := by sorry

end D1Bound5
end
