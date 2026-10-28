-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialWeightedCoeff_norm_le
-- name    : D1Bound5.halfBinomialWeightedCoeff_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:36:30.94382+00:00
-- url     : https://prove2.me/theorems/5effc6b3-924d-4303-8ab3-bec5a8d5b798
-- title:
--   Half Binomial Weighted Coeff norm le
-- statement:
--   The sharp real absolute convolution implies a uniform complex coefficient bound, without assuming x=y or positivity of either complex variable.
-- source:
--   D1Bound5/ComplexHalfBinomial.lean, lines 16-55, SHA-256 e7e6f8b11a6f554af427f9bfa36df35a8240f67bed0729f2ba7396a3dc39d624. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.halfBinomialWeightedCoeff_norm_le
    (x y : ℂ) (t : ℝ) (ht : 0 ≤ t)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (n : ℕ) (hn : 2 ≤ n) :
    ‖halfBinomialWeightedCoeff x y n‖ ≤
      4 * |halfBinomialCoeff n| * t ^ n := by sorry





end D1Bound5
end
