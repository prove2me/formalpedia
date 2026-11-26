-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_two_regular_colorable
-- name    : BrooksTheorem.Aux.two_regular_colorable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:40.16004+00:00
-- url     : https://prove2.me/theorems/7f342c72-6770-5e90-a107-a30f55a83260
-- title:
--   Aux: two regular colorable
-- statement:
--   A connected graph with all degrees equal to two which is not an odd cycle is
--   `2`-colourable.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L100-L124
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L100-L124

module
public import Definitions.Def_BrooksLib_BrooksCore
public import Definitions.Def_BrooksLib_Cycle
public import Definitions.Def_BrooksLib_BrooksLow
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*} [Fintype V]

theorem BrooksTheorem.Aux.two_regular_colorable (G : SimpleGraph V) (hconn : G.Connected)
    (h2 : ∀ v, (nb G v).card = 2) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable 2 := by sorry
