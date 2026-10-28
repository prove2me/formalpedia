-- Prove2me | Theorems.Thm_D1Bound5_homogeneousMultisetSum_insert
-- name    : D1Bound5.homogeneousMultisetSum_insert
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:31:11.628533+00:00
-- url     : https://prove2.me/theorems/5161386e-f892-4be3-8672-94db8dc8096c
-- title:
--   Homogeneous Multiset Sum insert
-- statement:
--   Finite-set variable adjunction, compatible with barycentric interpolation.
-- source:
--   D1Bound5/LagrangeHomogeneous.lean, lines 20-34, SHA-256 b4a9130e2e09325e0a7c90a60c13433e1e3d45746589329d45719e084b45b442. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Finset.Insert
import Mathlib.Data.Sym.Basic
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Polynomial Finset

namespace D1Bound5




theorem _root_.D1Bound5.homogeneousMultisetSum_insert
    {ι R : Type*} [DecidableEq ι] [CommSemiring R]
    (s : Finset ι) (a : ι → R) (t : ι) (ht : t ∉ s) (n : ℕ) :
    homogeneousMultisetSum (fun i : (insert t s : Finset ι) => a i) (n + 1) =
      a t * homogeneousMultisetSum (fun i : (insert t s : Finset ι) => a i) n +
        homogeneousMultisetSum (fun i : s => a i) (n + 1) := by sorry







end D1Bound5
end
