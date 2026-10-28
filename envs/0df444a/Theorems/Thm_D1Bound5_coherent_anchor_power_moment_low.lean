-- Prove2me | Theorems.Thm_D1Bound5_coherent_anchor_power_moment_low
-- name    : D1Bound5.coherent_anchor_power_moment_low
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:44:29.791487+00:00
-- url     : https://prove2.me/theorems/e35ffa37-ef50-4292-880c-542f42269ae7
-- title:
--   Coherent anchor power moment low
-- statement:
--   The low-degree moments in the coherent interpolation identity. The inverse-power form is the one obtained directly from a convergent Taylor series at each anchor.
-- source:
--   D1Bound5/CoherentAnalyticInterpolation.lean, lines 11-55, SHA-256 289b0bd79153d270dd2b679ca68b0d95c46f0054669b3b58cbc13d328e8ce08c. Project: https://github.com/tomislav-math/d1-bound5-lean

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


theorem _root_.D1Bound5.coherent_anchor_power_moment_low
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s)
    (n : ℕ) (hn : n < s.card) :
    (∑ i ∈ s, ((a i) ^ (s.card - 1) /
      (∏ j ∈ s.erase i, (a i - a j))) * ((a i)⁻¹) ^ n) =
      if n = 0 then 1 else 0 := by sorry











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
