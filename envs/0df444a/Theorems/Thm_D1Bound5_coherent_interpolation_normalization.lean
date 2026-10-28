-- Prove2me | Theorems.Thm_D1Bound5_coherent_interpolation_normalization
-- name    : D1Bound5.coherent_interpolation_normalization
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:18:38.349699+00:00
-- url     : https://prove2.me/theorems/4490b42e-b897-472c-8323-3584974c9bfe
-- title:
--   Coherent interpolation normalization
-- statement:
--   Algebraic normalization of the paper's coherent form. Here `g i` denotes the product of the two analytic square-root factors and `q` denotes the remaining square-root factor. The result applies to any nonzero choice of Vandermonde factor `Delta` and square-root scale `eta`. No denominator at an individual anchor is cancelled in this proof.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 250-278, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Sym.Card
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.Binomial
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset Polynomial

namespace D1Bound5













end D1Bound5




open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_interpolation_normalization
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a g : ι → ℂ) (q Delta eta : ℂ)
    (hm : 2 ≤ s.card) (hDelta : Delta ≠ 0) (heta : eta ≠ 0) :
    (-Delta * (eta * q) +
      ∑ i ∈ s, (Delta * (a i) ^ (s.card - 2) /
        (∏ j ∈ s.erase i, (a i - a j))) * (a i * eta * g i)) /
      (Delta * eta) =
      (∑ i ∈ s, ((a i) ^ (s.card - 1) /
        (∏ j ∈ s.erase i, (a i - a j))) * g i) - q := by sorry

end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
