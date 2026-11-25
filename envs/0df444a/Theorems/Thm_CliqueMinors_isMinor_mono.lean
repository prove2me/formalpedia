-- Prove2me | Theorems.Thm_CliqueMinors_isMinor_mono
-- name    : CliqueMinors.isMinor_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T19:38:33.748718+00:00
-- url     : https://prove2.me/theorems/19eb1f78-216e-4073-8638-c49c34d6ee42
-- title:
--   Clique Minors: is Minor mono
-- statement:
--   The Clique Minors construction uses the is Minor mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L105-L111
-- source:
--   https://github.com/jtraverso/hadwiger-mader/blob/a1ffd32233475c21ad474b2f80d57614911df9b0/CliqueMinorsLib/Minors.lean#L105-L111

module
public import Mathlib
public import Definitions.Def_CliqueMinorsLib_GraphOps
public import Definitions.Def_CliqueMinorsLib_Minors
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open CliqueMinors
variable {V W : Type*}
open Relation

theorem CliqueMinors.isMinor_mono {G G' : SimpleGraph V} {H : SimpleGraph W} (hle : G' ≤ G)
    (h : IsMinor H G') : IsMinor H G := by sorry
