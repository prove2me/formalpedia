-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_cut_case
-- name    : BrooksTheorem.Aux.cut_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:13.348305+00:00
-- url     : https://prove2.me/theorems/26fa281f-5a19-4f50-83b1-7625a3b8cf28
-- title:
--   Aux: cut case
-- statement:
--   Separation at a single vertex `z`: the set `B` is attached to the rest only through `z`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L376-L395
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksCore.lean#L376-L395

module
public import Definitions.Def_BrooksLib_Greedy
public import Definitions.Def_BrooksLib_BrooksCore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]

theorem BrooksTheorem.Aux.cut_case {k : ℕ} {H : SimpleGraph V} (ih : IHyp k H)
    (hdeg : ∀ v, (nb H v).card ≤ k) (hcf : H.CliqueFree (k + 1)) (B : Set V) {x z y0 b bn : V}
    (hxz : x ≠ z) (hxB : x ∉ B) (hxy : H.Adj x y0)
    (hBedge : ∀ u ∈ B, ∀ v, H.Adj u v → v ∈ B ∨ v = z) (hb : b ∈ B) (hbn : H.Adj b bn) :
    ∃ g : V → Fin k, Proper H g := by sorry
