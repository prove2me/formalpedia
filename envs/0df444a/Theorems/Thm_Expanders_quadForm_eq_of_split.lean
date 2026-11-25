-- Prove2me | Theorems.Thm_Expanders_quadForm_eq_of_split
-- name    : Expanders.quadForm_eq_of_split
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T15:08:55.153592+00:00
-- url     : https://prove2.me/theorems/70154ae8-1415-4093-83f6-e626b5fdf9a0
-- title:
--   Expanders: quad Form eq of split
-- statement:
--   Rewriting the quadratic form of a `d`-regular graph as `d ‖f‖²` minus a sum of oriented edge
--   contributions, given any splitting `c` of the edge terms `(f v - f w)²`.
--
--   Source: https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L78-L106
-- source:
--   https://github.com/jtraverso/expander-spectral/blob/f96a99893d4d31495af5f8d9e6181f7b4c91e0ba/ExpanderLib/NilliBall.lean#L78-L106

module
public import Mathlib
public import Definitions.Def_ExpanderLib_NilliBall
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Matrix Finset
open Expanders
variable {V : Type*} [Fintype V]

theorem Expanders.quadForm_eq_of_split (G : SimpleGraph V) [DecidableRel G.Adj] {d : ℕ}
    (hd : G.IsRegularOfDegree d) (f : V → ℝ) (c : V → V → ℝ)
    (hc : ∀ v, ∀ w ∈ G.neighborFinset v, (f v - f w) ^ 2 = c v w + c w v) :
    dotProduct f (G.adjMatrix ℝ *ᵥ f) =
      d * ∑ v, f v ^ 2 - ∑ v, ∑ w ∈ G.neighborFinset v, c v w := by sorry
