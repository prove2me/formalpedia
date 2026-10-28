-- Prove2me | Theorems.Thm_D1Bound5_coherent_interpolation_series_exact
-- name    : D1Bound5.coherent_interpolation_series_exact
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:37:16.072755+00:00
-- url     : https://prove2.me/theorems/b6a49ce9-ebe1-46c7-8c11-2caa55781dae
-- title:
--   Coherent interpolation series exact
-- statement:
--   Exact interpolation of a convergent complex Taylor series. This proves convergence of the homogeneous tail from convergence at the finitely many distinct nonzero anchors. No majorant or desired interpolation identity is included among the hypotheses.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 90-156, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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






theorem _root_.D1Bound5.coherent_interpolation_series_exact
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℂ) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s)
    (c : ℕ → ℂ) (g : ι → ℂ)
    (hc : ∀ i ∈ s, HasSum (fun n : ℕ => c n * ((a i)⁻¹) ^ n) (g i)) :
    Summable (fun k : ℕ => c (s.card + k) *
      MvPolynomial.aeval (fun i : s => (a i)⁻¹)
        (MvPolynomial.hsymm s ℂ k)) ∧
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) * g i) =
      c 0 + ((-1 : ℂ) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        ∑' k : ℕ, c (s.card + k) *
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
