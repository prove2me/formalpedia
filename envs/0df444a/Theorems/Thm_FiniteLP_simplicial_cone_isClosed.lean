-- Prove2me | Theorems.Thm_FiniteLP_simplicial_cone_isClosed
-- name    : FiniteLP.simplicial_cone_isClosed
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:27:08.5216+00:00
-- url     : https://prove2.me/theorems/63b02c5e-f796-537c-b6ec-af2df1fd6614
-- title:
--   Finite LP: simplicial cone is Closed
-- statement:
--   A simplicial cone (nonnegative combinations of a linearly independent finite family) is
--   closed: it is the image of the closed nonnegative orthant under an injective (hence closed)
--   linear map.
--
--   Source: https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L55-L93
-- source:
--   https://github.com/jtraverso/erdos-girth-chromatic/blob/05407c110b29ebb412667c688b2758d23bc744dd/FractionalLib/FiniteLPDuality.lean#L55-L93

module
public import Mathlib
public import Definitions.Def_FractionalLib_FiniteLPDuality
set_option autoImplicit true
@[expose] public section
public section
open scoped BigOperators InnerProductSpace
open Finset
open FiniteLP

theorem FiniteLP.simplicial_cone_isClosed {κ ι : Type*} [Fintype κ] [Fintype ι]
    (v : κ → EuclideanSpace ℝ ι) (s : Finset κ) (hli : LinearIndepOn ℝ v s) :
    IsClosed {y : EuclideanSpace ℝ ι |
      ∃ c : κ → ℝ, (∀ k, 0 ≤ c k) ∧ (∀ k ∉ s, c k = 0) ∧ ∑ k ∈ s, c k • v k = y} := by sorry
