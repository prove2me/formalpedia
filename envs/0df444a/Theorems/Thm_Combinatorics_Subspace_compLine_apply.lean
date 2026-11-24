-- Prove2me | Theorems.Thm_Combinatorics_Subspace_compLine_apply
-- name    : Combinatorics.Subspace.compLine_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T04:50:25.190179+00:00
-- url     : https://prove2.me/theorems/d5735559-c8eb-4bf8-82e9-cee248313f05
-- title:
--   Subspace: comp Line apply
-- statement:
--   The Subspace construction uses the comp Line apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Line.lean#L94-L96
-- source:
--   https://github.com/gdahia/ShelahHalesJewett/blob/8a91fc0e8a9617f8ade16ccb3b56e543990c9f45/ShelahHalesJewett/Line.lean#L94-L96

module
public import Mathlib.Combinatorics.HalesJewett
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Pigeonhole
public import Definitions.Def_ShelahHalesJewett_Line
set_option autoImplicit true
@[expose] public section
public section
open Combinatorics
variable {η α ι ι' κ : Type*}
open Combinatorics.Subspace

theorem Combinatorics.Subspace.compLine_apply (V : Subspace η α ι) (l : Line α η) (x : α) : V.compLine l x = V (l x) := by sorry
