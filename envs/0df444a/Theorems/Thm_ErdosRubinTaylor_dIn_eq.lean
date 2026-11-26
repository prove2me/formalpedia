-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_eq
-- name    : ErdosRubinTaylor.dIn_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:27:42.953958+00:00
-- url     : https://prove2.me/theorems/2e90f039-6c51-5cb0-b130-051f8a739cb9
-- title:
--   Erdos Rubin Taylor: d In eq
-- statement:
--   The Erdos Rubin Taylor construction uses the d In eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L132-L134
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L132-L134

module
public import Mathlib
public import Definitions.Def_ChoosabilityLib_ERTBasic
set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open ErdosRubinTaylor
variable {V : Type*}
variable [Fintype V]

theorem ErdosRubinTaylor.dIn_eq (G : SimpleGraph V) (T : Set V) (v : V) [DecidablePred (· ∈ T)]
    [DecidableRel G.Adj] : dIn G T v = (univ.filter (fun u => u ∈ T ∧ G.Adj v u)).card := by sorry
