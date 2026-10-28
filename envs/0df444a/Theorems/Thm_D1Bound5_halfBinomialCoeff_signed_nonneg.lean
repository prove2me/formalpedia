-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_signed_nonneg
-- name    : D1Bound5.halfBinomialCoeff_signed_nonneg
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:52.667243+00:00
-- url     : https://prove2.me/theorems/6362e0f4-9344-4c1e-aca4-5b8732595850
-- title:
--   Half Binomial Coeff signed nonneg
-- statement:
--   The coefficients have alternating signs from degree one onward.
-- source:
--   D1Bound5/HalfBinomialCoefficients.lean, lines 22-54, SHA-256 97b0412384b100b3ac306cb8297135156f099ce2af7ece88037027b2b15bd23b. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.halfBinomialCoeff_signed_nonneg (n : ℕ) :
    0 ≤ (-1 : ℝ) ^ n * halfBinomialCoeff (n + 1) := by sorry











end D1Bound5
end
