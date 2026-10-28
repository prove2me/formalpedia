-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_recurrence
-- name    : D1Bound5.halfBinomialCoeff_recurrence
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:43:40.238992+00:00
-- url     : https://prove2.me/theorems/b8c2b9a5-9699-4d25-b6d5-b436f160af01
-- title:
--   Half Binomial Coeff recurrence
-- statement:
--   The half-binomial coefficient recurrence in every degree.
-- source:
--   D1Bound5/HalfBinomialCoefficients.lean, lines 13-20, SHA-256 97b0412384b100b3ac306cb8297135156f099ce2af7ece88037027b2b15bd23b. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.halfBinomialCoeff_recurrence (n : ℕ) :
    (n + 1 : ℝ) * halfBinomialCoeff (n + 1) =
      ((1 / 2 : ℝ) - n) * halfBinomialCoeff n := by sorry













end D1Bound5
end
