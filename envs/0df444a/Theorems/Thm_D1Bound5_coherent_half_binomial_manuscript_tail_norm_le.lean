-- Prove2me | Theorems.Thm_D1Bound5_coherent_half_binomial_manuscript_tail_norm_le
-- name    : D1Bound5.coherent_half_binomial_manuscript_tail_norm_le
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:25:03.274839+00:00
-- url     : https://prove2.me/theorems/e30cace6-183a-422b-a093-9be6082ed7c2
-- title:
--   Coherent half binomial manuscript tail norm le
-- statement:
--   The complete homogeneous remainder estimate in the manuscript's parameters. There are exactly `s.card` reciprocal anchors. The estimate applies to the genuine complex half-binomial coefficients, and the full series defining `F_m` is proved summable.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 289-327, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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













end D1Bound5




open Finset

namespace D1Bound5



end D1Bound5




open Finset

namespace D1Bound5


theorem _root_.D1Bound5.coherent_half_binomial_manuscript_tail_norm_le
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (hs : s.Nonempty)
    (x y : ℂ) (A P : ℝ)
    (hA : 0 < A) (hP : 0 < P)
    (ha : ∀ i ∈ s, A ≤ ‖a i‖)
    (hx : ‖x‖ ≤ 1 / P) (hy : ‖y‖ ≤ 1 / P)
    (hAP : 1 < A * P) :
    Summable (fun j : ℕ => halfBinomialWeightedCoeff x y (s.card + j) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ j)) ∧
    ‖(∑' j : ℕ, halfBinomialWeightedCoeff x y (s.card + j) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ j)) -
      halfBinomialWeightedCoeff x y s.card‖ ≤
      (4 * |halfBinomialCoeff (s.card + 1)|) / P ^ s.card *
        (1 / (1 - 1 / (A * P)) ^ s.card - 1) := by sorry



end D1Bound5




namespace D1Bound5









end D1Bound5
end
