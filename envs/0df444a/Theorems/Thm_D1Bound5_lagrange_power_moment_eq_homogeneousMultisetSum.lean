-- Prove2me | Theorems.Thm_D1Bound5_lagrange_power_moment_eq_homogeneousMultisetSum
-- name    : D1Bound5.lagrange_power_moment_eq_homogeneousMultisetSum
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:35.547182+00:00
-- url     : https://prove2.me/theorems/944d551e-be26-42f1-867f-b6e6bc994530
-- title:
--   Lagrange power moment eq homogeneous Multiset Sum
-- statement:
--   Every higher Lagrange power moment is the complete homogeneous multiset sum, for every nonempty finite set of distinct nodes.
-- source:
--   D1Bound5/LagrangeHomogeneous.lean, lines 51-101, SHA-256 b4a9130e2e09325e0a7c90a60c13433e1e3d45746589329d45719e084b45b442. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Polynomial Finset

namespace D1Bound5








theorem _root_.D1Bound5.lagrange_power_moment_eq_homogeneousMultisetSum
    {F ι : Type*} [Field F] [DecidableEq ι]
    (s : Finset ι) (a : ι → F) (hs : s.Nonempty)
    (hinj : Set.InjOn a s) (k : ℕ) :
    (∑ i ∈ s, (a i) ^ (s.card - 1 + k) /
      (∏ j ∈ s.erase i, (a i - a j))) =
      homogeneousMultisetSum (fun i : s => a i) k := by sorry



end D1Bound5
end
