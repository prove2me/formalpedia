-- Prove2me | Theorems.Thm_ErdosRubinTaylor_gallai_mono
-- name    : ErdosRubinTaylor.gallai_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:02.811461+00:00
-- url     : https://prove2.me/theorems/2663c652-47ee-55c4-a145-700d3281237f
-- title:
--   Erdos Rubin Taylor: gallai mono
-- statement:
--   The Erdos Rubin Taylor construction uses the gallai mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L36-L37
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L36-L37

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.gallai_mono {T T' : Set V} (h : Gallai G T) (hsub : T' ⊆ T) : Gallai G T' := by sorry
