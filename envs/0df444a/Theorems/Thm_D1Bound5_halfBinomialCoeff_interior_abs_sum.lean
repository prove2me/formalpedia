-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_interior_abs_sum
-- name    : D1Bound5.halfBinomialCoeff_interior_abs_sum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:00.647567+00:00
-- url     : https://prove2.me/theorems/81f1df39-74c1-4480-b3eb-c7255663a13d
-- title:
--   Half Binomial Coeff interior abs sum
-- statement:
--   The interior absolute convolution is exactly twice the endpoint modulus.
-- source:
--   D1Bound5/HalfBinomialConvolutionAbs.lean, lines 44-68, SHA-256 1173ab778ae4d08a2f4654331009133181881091b647e271ed67fd57519e3d85. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.halfBinomialCoeff_interior_abs_sum (k : ℕ) :
    (∑ ij ∈ Finset.antidiagonal k,
      |halfBinomialCoeff (ij.1 + 1) * halfBinomialCoeff (ij.2 + 1)|) =
        2 * |halfBinomialCoeff (k + 2)| := by sorry



end D1Bound5
end
