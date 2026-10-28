-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_pair_abs_signed
-- name    : D1Bound5.halfBinomialCoeff_pair_abs_signed
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:01.964297+00:00
-- url     : https://prove2.me/theorems/ff217900-eae3-4092-9eba-c645df4de00b
-- title:
--   Half Binomial Coeff pair abs signed
-- statement:
--   All products of positive-degree coefficients have the prescribed sign.
-- source:
--   D1Bound5/HalfBinomialConvolutionAbs.lean, lines 32-42, SHA-256 1173ab778ae4d08a2f4654331009133181881091b647e271ed67fd57519e3d85. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.halfBinomialCoeff_pair_abs_signed (i j : ℕ) :
    |halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1)| =
       (-1 : ℝ) ^ (i + j + 2) *
         (halfBinomialCoeff (i + 1) * halfBinomialCoeff (j + 1)) := by sorry





end D1Bound5
end
