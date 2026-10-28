-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_cauchy_hasSum
-- name    : D1Bound5.halfBinomialCoeff_cauchy_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:51:07.975503+00:00
-- url     : https://prove2.me/theorems/f799d2d5-7e0e-404b-aa15-bd7d2d367cff
-- title:
--   Half Binomial Coeff cauchy has Sum
-- statement:
--   The full Cauchy product of the two half-binomial series converges absolutely to the product of their principal complex powers.
-- source:
--   D1Bound5/HalfBinomialAnalytic.lean, lines 19-35, SHA-256 109e12b103be56576f2b508ea1bde2f80f1c2a5c9319f282768950102447591a. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
namespace D1Bound5




theorem _root_.D1Bound5.halfBinomialCoeff_cauchy_hasSum (x y z : ℂ)
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    HasSum (fun n : ℕ => ∑ ij ∈ Finset.antidiagonal n,
      ((halfBinomialCoeff ij.1 : ℂ) * (x * z) ^ ij.1) *
      ((halfBinomialCoeff ij.2 : ℂ) * (y * z) ^ ij.2))
      (((1 + x * z) ^ (1 / 2 : ℂ)) * ((1 + y * z) ^ (1 / 2 : ℂ))) := by sorry





end D1Bound5
end
