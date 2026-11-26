-- Prove2me | Theorems.Thm_BrooksTheorem_Aux_top_of_clique
-- name    : BrooksTheorem.Aux.top_of_clique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:33:31.189785+00:00
-- url     : https://prove2.me/theorems/ce89d604-5670-47a5-9898-b24d5bd6ef3d
-- title:
--   Aux: top of clique
-- statement:
--   A connected graph with all degrees at most `d` containing a `(d + 1)`-clique is complete.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L40-L66
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/BrooksLow.lean#L40-L66

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

theorem BrooksTheorem.Aux.top_of_clique (G : SimpleGraph V) (hconn : G.Connected) {d : ℕ}
    (hdeg : ∀ v, (nb G v).card ≤ d) (K : Finset V) (hK : G.IsNClique (d + 1) K) : G = ⊤ := by sorry
