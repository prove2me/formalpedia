-- Prove2me | Theorems.Thm_D1Bound5_halfBinomialCoeff_hasSum_cpow
-- name    : D1Bound5.halfBinomialCoeff_hasSum_cpow
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:37:46.550201+00:00
-- url     : https://prove2.me/theorems/7a9c2b1b-e040-4699-850e-ad7fca0763ee
-- title:
--   Half Binomial Coeff has Sum cpow
-- statement:
--   The half-binomial coefficients sum to the complex principal power of exponent one half throughout the open unit disk.
-- source:
--   D1Bound5/HalfBinomialAnalytic.lean, lines 6-17, SHA-256 109e12b103be56576f2b508ea1bde2f80f1c2a5c9319f282768950102447591a. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.halfBinomialCoeff_hasSum_cpow (z : ℂ) (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (halfBinomialCoeff n : ℂ) * z ^ n)
      ((1 + z) ^ (1 / 2 : ℂ)) := by sorry







end D1Bound5
end
