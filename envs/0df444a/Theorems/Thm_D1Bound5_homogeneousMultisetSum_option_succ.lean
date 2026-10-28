-- Prove2me | Theorems.Thm_D1Bound5_homogeneousMultisetSum_option_succ
-- name    : D1Bound5.homogeneousMultisetSum_option_succ
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T03:35:32.62373+00:00
-- url     : https://prove2.me/theorems/9dd14143-9f9c-48d6-8de5-90c45aa04302
-- title:
--   Homogeneous Multiset Sum option succ
-- statement:
--   When a new variable is adjoined, the complete homogeneous polynomial satisfies a one-step recursion at every positive degree.
-- source:
--   D1Bound5/HomogeneousSymmetric.lean, lines 27-47, SHA-256 9ca0c1b5630feef5d0a34c972d9c43d84be51f3ce74b855f5c9873ea76bd8466. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Finset Multiset Sym

namespace D1Bound5






theorem _root_.D1Bound5.homogeneousMultisetSum_option_succ
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a : Option ι → R) (n : ℕ) :
    homogeneousMultisetSum a (n + 1) =
      a none * homogeneousMultisetSum a n +
        homogeneousMultisetSum (fun i : ι => a (some i)) (n + 1) := by sorry









end D1Bound5
end
