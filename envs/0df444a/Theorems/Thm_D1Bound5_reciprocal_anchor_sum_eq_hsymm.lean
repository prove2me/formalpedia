-- Prove2me | Theorems.Thm_D1Bound5_reciprocal_anchor_sum_eq_hsymm
-- name    : D1Bound5.reciprocal_anchor_sum_eq_hsymm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:28:14.106433+00:00
-- url     : https://prove2.me/theorems/28a84877-3392-466e-b45a-40fb286045fe
-- title:
--   Reciprocal anchor sum eq hsymm
-- statement:
--   The all-order negative-power interpolation identity from the frozen manuscript, with its exact parity sign and product denominator.
-- source:
--   D1Bound5/InterpolationWeights.lean, lines 8-25, SHA-256 f0694cf6e24749b6ebbea5b804a44acbab942bf3fc03c6d3a67996fffcda18a7. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs

section
open Finset

namespace D1Bound5


theorem _root_.D1Bound5.reciprocal_anchor_sum_eq_hsymm
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (ha : ∀ i ∈ s, a i ≠ 0) (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, ((a i)⁻¹) ^ (k + 1) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      ((-1 : F) ^ (s.card - 1) * (∏ i ∈ s, a i)⁻¹) *
        MvPolynomial.aeval (fun i : s => (a i)⁻¹) (MvPolynomial.hsymm s F k) := by sorry

end D1Bound5
end
