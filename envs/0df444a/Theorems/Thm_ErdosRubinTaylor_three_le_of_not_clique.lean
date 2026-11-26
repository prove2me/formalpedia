-- Prove2me | Theorems.Thm_ErdosRubinTaylor_three_le_of_not_clique
-- name    : ErdosRubinTaylor.three_le_of_not_clique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:31:21.932475+00:00
-- url     : https://prove2.me/theorems/079f9f68-8886-4280-af19-59d67f883f25
-- title:
--   Erdos Rubin Taylor: three le of not clique
-- statement:
--   The Erdos Rubin Taylor construction uses the three le of not clique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L39-L58
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L39-L58

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_ChoosabilityLib_ERTGallai
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*} {G : SimpleGraph V}

theorem ErdosRubinTaylor.three_le_of_not_clique [Finite V] {T : Set V} (hT : SConn G T) (hK : ¬ IsCliqueOn G T) :
    3 ≤ T.ncard := by sorry
