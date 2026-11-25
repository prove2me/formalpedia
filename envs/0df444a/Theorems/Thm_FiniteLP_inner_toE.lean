-- Prove2me | Theorems.Thm_FiniteLP_inner_toE
-- name    : FiniteLP.inner_toE
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:15.172546+00:00
-- url     : https://prove2.me/theorems/75b796c9-99b2-4137-bc11-146b20cf4833
-- title:
--   Finite LP: inner to E
-- statement:
--   The Finite LP construction uses the inner to E property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L45-L48
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L45-L48

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP

theorem FiniteLP.inner_toE {ι : Type*} [Fintype ι] (f : ι → ℝ) (y : EuclideanSpace ℝ ι) :
    (inner ℝ (toE f) y) = ∑ i, f i * y i := by sorry
