-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_abs_next_le
-- name    : D1Bound5.halfBinomialCoeff_abs_next_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:37.649208+00:00
-- url     : https://prove2.me/theorems/5a18bd3a-9ca1-4ec9-be97-3a122cc0b051
-- title:
--   Half Binomial Coeff abs next le
-- statement:
--   Absolute coefficients weakly decrease from degree one onward.
-- source:
--   D1Bound5/HalfBinomialCoefficients.lean, lines 56-72, SHA-256 97b0412384b100b3ac306cb8297135156f099ce2af7ece88037027b2b15bd23b. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.halfBinomialCoeff_abs_next_le (n : ℕ) (hn : 1 ≤ n) :
    |halfBinomialCoeff (n + 1)| ≤ |halfBinomialCoeff n| := by sorry









end D1Bound5
end
