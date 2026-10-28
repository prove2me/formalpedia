-- Prove2me | Theorems.Thm_D1Bound5_homogeneousMultisetSum_eq_hsymm
-- name    : D1Bound5.homogeneousMultisetSum_eq_hsymm
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:33.240342+00:00
-- url     : https://prove2.me/theorems/e6592099-382a-4f98-b62a-9605f17c59a3
-- title:
--   Homogeneous Multiset Sum eq hsymm
-- statement:
--   The multiset sum agrees at every degree with mathlib's hsymm under evaluation.
-- source:
--   D1Bound5/HomogeneousSymmetric.lean, lines 15-25, SHA-256 9ca0c1b5630feef5d0a34c972d9c43d84be51f3ce74b855f5c9873ea76bd8466. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Data.Sym.Basic
import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
import Definitions.Def_D1Bound5_HomogeneousSymmetric_Definitions

section
open Finset Multiset Sym

namespace D1Bound5




theorem _root_.D1Bound5.homogeneousMultisetSum_eq_hsymm
    {ι R : Type*} [Fintype ι] [DecidableEq ι] [CommSemiring R]
    (a : ι → R) (n : ℕ) :
    homogeneousMultisetSum a n =
      MvPolynomial.aeval a (MvPolynomial.hsymm ι R n) := by sorry











end D1Bound5
end
