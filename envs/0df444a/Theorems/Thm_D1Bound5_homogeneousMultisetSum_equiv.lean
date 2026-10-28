-- Prove2me | Theorems.Thm_D1Bound5_homogeneousMultisetSum_equiv
-- name    : D1Bound5.homogeneousMultisetSum_equiv
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:33:50.79026+00:00
-- url     : https://prove2.me/theorems/5dbaedb5-20cb-4b87-9f98-97c1e9f35f5a
-- title:
--   Homogeneous Multiset Sum equiv
-- statement:
--   Reindexing variables preserves the explicit homogeneous multiset sum.
-- source:
--   D1Bound5/LagrangeHomogeneous.lean, lines 9-18, SHA-256 b4a9130e2e09325e0a7c90a60c13433e1e3d45746589329d45719e084b45b442. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Polynomial Finset

namespace D1Bound5


theorem _root_.D1Bound5.homogeneousMultisetSum_equiv
    {ι κ R : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype κ] [DecidableEq κ] [CommSemiring R]
    (e : ι ≃ κ) (a : κ → R) (n : ℕ) :
    homogeneousMultisetSum (fun i => a (e i)) n = homogeneousMultisetSum a n := by sorry









end D1Bound5
end
