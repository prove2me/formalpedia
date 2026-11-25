-- Prove2me | Theorems.Thm_AllOnesLab_asPoly_irreducible
-- name    : AllOnesLab.asPoly_irreducible
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T20:56:45.511255+00:00
-- url     : https://prove2.me/theorems/ac617259-df9d-40e2-965f-2f401827c079
-- title:
--   All Ones Lab: as Poly irreducible
-- statement:
--   Over a finite extension of `𝔽₂`, `X² + X + a` is irreducible as soon as `Tr(a) ≠ 0`:
--   a root would exhibit `a` as `z² + z`, which has trace `0`.
--
--   Source: https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Hard.lean#L59-L71
-- source:
--   https://github.com/BrandonMYates/allones-comparator/blob/76f3a65407c45de21228824f7a41430acec473a4/AllOnesLab/Hard.lean#L59-L71

import Definitions.Def_AllOnesLab_Trace
import Definitions.Def_AllOnesLab_Hard
set_option autoImplicit true
open Polynomial
open AllOnesLab
variable {K : Type*} [Field K] [Algebra (ZMod 2) K] [FiniteDimensional (ZMod 2) K]

theorem AllOnesLab.asPoly_irreducible (a : K) (ha : Algebra.trace (ZMod 2) K a ≠ 0) :
    Irreducible (asPoly a) := by sorry
