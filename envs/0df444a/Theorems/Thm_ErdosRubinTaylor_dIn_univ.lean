-- Prove2me | Theorems.Thm_ErdosRubinTaylor_dIn_univ
-- name    : ErdosRubinTaylor.dIn_univ
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:29:19.887801+00:00
-- url     : https://prove2.me/theorems/3e0d960f-6660-4a21-8890-1db0b2395c63
-- title:
--   Erdos Rubin Taylor: d In univ
-- statement:
--   The Erdos Rubin Taylor construction uses the d In univ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L136-L139
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/ChoosabilityLib/ERTBasic.lean#L136-L139

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

theorem ErdosRubinTaylor.dIn_univ (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) :
    dIn G Set.univ v = G.degree v := by sorry
