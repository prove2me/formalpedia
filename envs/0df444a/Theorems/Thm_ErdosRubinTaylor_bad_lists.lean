-- Prove2me | Theorems.Thm_ErdosRubinTaylor_bad_lists
-- name    : ErdosRubinTaylor.bad_lists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:36:01.521412+00:00
-- url     : https://prove2.me/theorems/597b27f3-3fbc-439a-860d-1d62812a03d5
-- title:
--   Erdos Rubin Taylor: bad lists
-- statement:
--   A connected Gallai set has a degree list assignment with no proper colouring.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L246-L381
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L246-L381

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

theorem ErdosRubinTaylor.bad_lists (G : SimpleGraph V) : ∀ n, ∀ T : Set V, T.ncard = n → SConn G T →
    Gallai G T →
    ∃ L : V → Finset ℕ, (∀ v ∈ T, dIn G T v ≤ (L v).card) ∧ ¬ ColIn G T L := by sorry
