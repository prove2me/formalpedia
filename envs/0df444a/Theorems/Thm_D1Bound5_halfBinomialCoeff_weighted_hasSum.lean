-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_weighted_hasSum
-- name    : D1Bound5.halfBinomialCoeff_weighted_hasSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:46:27.270905+00:00
-- url     : https://prove2.me/theorems/59ed09ae-47bc-4623-9464-ad5bae5b33f5
-- title:
--   Half Binomial Coeff weighted has Sum
-- statement:
--   Exact convergence of the weighted two-variable half-binomial series to the corresponding product of complex square-root powers.
-- source:
--   D1Bound5/HalfBinomialAnalytic.lean, lines 59-70, SHA-256 109e12b103be56576f2b508ea1bde2f80f1c2a5c9319f282768950102447591a. Project: https://github.com/tomislav-math/d1-bound5-lean

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








theorem _root_.D1Bound5.halfBinomialCoeff_weighted_hasSum (x y z : ℂ)
    (hx : ‖x * z‖ < 1) (hy : ‖y * z‖ < 1) :
    HasSum (fun n : ℕ =>
      (∑ ij ∈ Finset.antidiagonal n,
        ((halfBinomialCoeff ij.1 * halfBinomialCoeff ij.2 : ℝ) : ℂ) *
          x ^ ij.1 * y ^ ij.2) * z ^ n)
      (((1 + x * z) ^ (1 / 2 : ℂ)) * ((1 + y * z) ^ (1 / 2 : ℂ))) := by sorry

end D1Bound5
end
