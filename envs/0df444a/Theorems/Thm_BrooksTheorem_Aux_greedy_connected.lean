-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_greedy_connected
-- name    : BrooksTheorem.Aux.greedy_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:00.874918+00:00
-- url     : https://prove2.me/theorems/6d267b38-76ef-44ca-a121-cbf123a92e78
-- title:
--   Aux: greedy connected
-- statement:
--   Greedy colouring of a connected graph having a vertex of degree less than `k`.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L81-L96
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L81-L96

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

theorem BrooksTheorem.Aux.greedy_connected (G : SimpleGraph V) (hconn : G.Connected) (k : ℕ)
    (hdeg : ∀ v, (nb G v).card ≤ k) (hdef : ∃ v0, (nb G v0).card < k) :
    ∃ f : V → Fin k, Proper G f := by sorry
