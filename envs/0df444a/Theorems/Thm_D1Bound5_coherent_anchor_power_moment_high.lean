-- Prove2me | Theorems.Thm_D1Bound5_coherent_anchor_power_moment_high
-- name    : D1Bound5.coherent_anchor_power_moment_high
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:23.462229+00:00
-- url     : https://prove2.me/theorems/fc128893-e726-4007-ac72-6668d1d978c0
-- title:
--   Coherent anchor power moment high
-- statement:
--   Every remaining Taylor moment is a complete homogeneous polynomial in the reciprocal anchors, with the exact sign and product denominator.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 57-88, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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




theorem _root_.D1Bound5.coherent_anchor_power_moment_high
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ (s.card + k)) =
      ((-1 : F) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        MvPolynomial.aeval (fun i : s => (a i)⁻¹)
          (MvPolynomial.hsymm s F k) := by sorry









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
