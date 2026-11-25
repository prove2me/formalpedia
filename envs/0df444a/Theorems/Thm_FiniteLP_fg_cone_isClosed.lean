-- Prove2me | Theorems.Thm_FiniteLP_fg_cone_isClosed
-- name    : FiniteLP.fg_cone_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:36.697979+00:00
-- url     : https://prove2.me/theorems/43544fed-5efe-4938-8463-27dd6c28374d
-- title:
--   Finite LP: fg cone is Closed
-- statement:
--   The finitely generated cone `{∑ k c k • v k : c ≥ 0}` is closed.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L169-L188
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L169-L188

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP

theorem FiniteLP.fg_cone_isClosed {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) :
    IsClosed {y : EuclideanSpace ℝ ι | ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ ∑ k, c k • v k = y} := by sorry
