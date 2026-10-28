-- Prove2me | Theorems.Thm_D1Bound5_coherent_half_binomial_exact
-- name    : D1Bound5.coherent_half_binomial_exact
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:20:54.088047+00:00
-- url     : https://prove2.me/theorems/3dc8fefc-99bc-41f4-a591-2df687305ce7
-- title:
--   Coherent half binomial exact
-- statement:
--   The manuscript's exact coherent interpolation identity for the actual principal square-root products, before multiplying by the Vandermonde and the chosen square root of `pq`. All analytic convergence is proved.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 158-184, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

section
open Finset Polynomial

namespace D1Bound5








theorem _root_.D1Bound5.coherent_half_binomial_exact
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s)
    (x y : ℂ)
    (hx : ∀ i ∈ s, ‖x * (a i)⁻¹‖ < 1)
    (hy : ∀ i ∈ s, ‖y * (a i)⁻¹‖ < 1) :
    Summable (fun k : ℕ => halfBinomialWeightedCoeff x y (s.card + k) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ k)) ∧
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) *
        (((1 + x * (a i)⁻¹) ^ (1 / 2 : ℂ)) *
          ((1 + y * (a i)⁻¹) ^ (1 / 2 : ℂ)))) =
      1 + ((-1 : ℂ) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        ∑' k : ℕ, halfBinomialWeightedCoeff x y (s.card + k) *
          MvPolynomial.aeval (fun i : s => (a i)⁻¹)
            (MvPolynomial.hsymm s ℂ k) := by sorry





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
