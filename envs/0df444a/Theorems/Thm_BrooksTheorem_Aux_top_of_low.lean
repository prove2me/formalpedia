-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_top_of_low
-- name    : BrooksTheorem.Aux.top_of_low
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:42.150827+00:00
-- url     : https://prove2.me/theorems/53fc42ce-7fe0-57d0-9084-8431c2fa9578
-- title:
--   Aux: top of low
-- statement:
--   A connected graph with all degrees at most `d ≤ 1` and a vertex of degree `d` is complete.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L69-L78
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L69-L78

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

theorem BrooksTheorem.Aux.top_of_low (G : SimpleGraph V) (hconn : G.Connected) {d : ℕ} (hd : d ≤ 1)
    (hdeg : ∀ v, (nb G v).card ≤ d) (v : V) (hv : (nb G v).card = d) : G = ⊤ := by sorry
