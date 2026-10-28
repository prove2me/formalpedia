-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_convolution_zero
-- name    : D1Bound5.halfBinomialCoeff_convolution_zero
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:01.49438+00:00
-- url     : https://prove2.me/theorems/b9bb7230-6511-42de-8cec-412735030bb7
-- title:
--   Half Binomial Coeff convolution zero
-- statement:
--   The half-binomial convolution vanishes at each degree at least two.
-- source:
--   D1Bound5/HalfBinomialCoefficients.lean, lines 101-112, SHA-256 97b0412384b100b3ac306cb8297135156f099ce2af7ece88037027b2b15bd23b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
















theorem _root_.D1Bound5.halfBinomialCoeff_convolution_zero (n : ℕ) (hn : 2 ≤ n) :
    (∑ ij ∈ Finset.antidiagonal n,
        halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2) = 0 := by sorry

end D1Bound5
end
