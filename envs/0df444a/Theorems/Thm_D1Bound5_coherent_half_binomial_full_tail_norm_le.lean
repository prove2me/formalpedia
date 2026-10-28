-- Prove2me | Theorems.Thm_D1Bound5_coherent_half_binomial_full_tail_norm_le
-- name    : D1Bound5.coherent_half_binomial_full_tail_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:42:36.506275+00:00
-- url     : https://prove2.me/theorems/a0efab92-806d-40ce-b92f-1c0b5944d271
-- title:
--   Coherent half binomial full tail norm le
-- statement:
--   The full homogeneous tail is summable, and its difference from the leading coefficient satisfies precisely the paper's sharp remainder bound. This is the `F_m - f_m` form of the existing positive-tail bound.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 213-239, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_ComplexHalfBinomial_Definitions
import Definitions.Def_D1Bound5_HalfBinomialCoefficients_Definitions

section
open Finset Polynomial

namespace D1Bound5












theorem _root_.D1Bound5.coherent_half_binomial_full_tail_norm_le
    {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (a : ι → ℂ) (x y : ℂ) (m : ℕ) (ρ t : ℝ)
    (hm : 1 ≤ m) (hρ0 : 0 ≤ ρ) (ht : 0 ≤ t)
    (ha : ∀ i, ‖a i‖ ≤ ρ)
    (hx : ‖x‖ ≤ t) (hy : ‖y‖ ≤ t)
    (hradius : ρ * t < 1) :
    Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (m + j) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ j)) ∧
    ‖(∑' j : ℕ, halfBinomialWeightedCoeff x y (m + j) *
      MvPolynomial.aeval a (MvPolynomial.hsymm ι ℂ j)) -
        halfBinomialWeightedCoeff x y m‖ ≤
      (4 * |halfBinomialCoeff (m + 1)|) * t ^ m *
        (1 / (1 - ρ * t) ^ Fintype.card ι - 1) := by sorry

end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5





end D1Bound5




namespace D1Bound5









end D1Bound5
end
