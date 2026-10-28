-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_tail_norm_le
-- name    : D1Bound5.halfBinomialWeightedCoeff_tail_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:32.610612+00:00
-- url     : https://prove2.me/theorems/a301fc9b-b94e-41b1-8269-23472c04f57c
-- title:
--   Half Binomial Weighted Coeff tail norm le
-- statement:
--   The monotonicity of the half-binomial coefficients gives one fixed envelope for every degree at least m+1, when m is positive.
-- source:
--   D1Bound5/ComplexHalfBinomial.lean, lines 57-75, SHA-256 e7e6f8b11a6f554af427f9bfa36df35a8240f67bed0729f2ba7396a3dc39d624. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset

namespace D1Bound5






theorem _root_.D1Bound5.halfBinomialWeightedCoeff_tail_norm_le
    (x y : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (m n : ℕ) (hm : 1 ≤ m) (hn : m + 1 ≤ n) :
    ‖halfBinomialWeightedCoeff x y n‖ ≤
      4 * |halfBinomialCoeff (m + 1)| * t ^ n := by sorry



end D1Bound5
end
