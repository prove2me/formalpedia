-- Prove2me | Theorems.Thm_ErdosRubinTaylor_exists_third
-- name    : ErdosRubinTaylor.exists_third
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:35:19.745461+00:00
-- url     : https://prove2.me/theorems/50333280-20ff-5456-8afc-f44804b75155
-- title:
--   Erdos Rubin Taylor: exists third
-- statement:
--   The Erdos Rubin Taylor construction uses the exists third property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTChoosable.lean#L29-L39
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTChoosable.lean#L29-L39

module
public import Definitions.Def_ChoosabilityLib_ERTBasic
public import Definitions.Def_BrooksLib_Brooks
public import Definitions.Def_ChoosabilityLib_ERTChoosable
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}

theorem ErdosRubinTaylor.exists_third {S : Set V} (h3 : 3 ≤ S.ncard) (a b : V) : ∃ x ∈ S, x ≠ a ∧ x ≠ b := by sorry
