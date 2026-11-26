-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_clique
-- name    : ErdosRubinTaylor.dIn_clique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:42.469062+00:00
-- url     : https://prove2.me/theorems/f172fc6c-04a3-56a4-ab21-2787151ea865
-- title:
--   Erdos Rubin Taylor: d In clique
-- statement:
--   The Erdos Rubin Taylor construction uses the d In clique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L192-L202
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L192-L202

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}
variable [Fintype V]

theorem ErdosRubinTaylor.dIn_clique {T : Set V} (hK : IsCliqueOn G T) {u : V} (hu : u ∈ T) :
    dIn G T u = T.ncard - 1 := by sorry
