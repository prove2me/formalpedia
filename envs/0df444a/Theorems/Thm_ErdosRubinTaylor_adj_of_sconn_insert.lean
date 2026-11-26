-- Prove2me | Theorems.Thm_ErdosRubinTaylor_adj_of_sconn_insert
-- name    : ErdosRubinTaylor.adj_of_sconn_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:57.036253+00:00
-- url     : https://prove2.me/theorems/0f94fa29-21a6-49ad-8037-3973f6eab5be
-- title:
--   Erdos Rubin Taylor: adj of sconn insert
-- statement:
--   The Erdos Rubin Taylor construction uses the adj of sconn insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L97-L105
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L97-L105

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.adj_of_sconn_insert {D : Set V} {x : V} (h : SConn G (insert x D)) (hne : D.Nonempty)
    (hxD : x ∉ D) : ∃ d ∈ D, G.Adj x d := by sorry
