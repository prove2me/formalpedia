-- Prove2me | Theorems.Thm_ErdosRubinTaylor_block_regular
-- name    : ErdosRubinTaylor.block_regular
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:56.22514+00:00
-- url     : https://prove2.me/theorems/edc9fa89-dfc3-4694-9871-002963485ef6
-- title:
--   Erdos Rubin Taylor: block regular
-- statement:
--   The Erdos Rubin Taylor construction uses the block regular property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L220-L225
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTGallai.lean#L220-L225

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

theorem ErdosRubinTaylor.block_regular {T : Set V}
    (h : IsCliqueOn G T ∨ ∃ n, Odd n ∧ Nonempty (G.induce T ≃g cycleGraph n))
    (h2 : 2 ≤ T.ncard) {u v : V} (hu : u ∈ T) (hv : v ∈ T) : dIn G T u = dIn G T v := by sorry
