-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_gram_eq_source_vertices
-- name    : DeletionCode.SignedSupport.gram_eq_source_vertices
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:07:54.540103+00:00
-- url     : https://prove2.me/theorems/67f668a8-aa21-4947-8160-65f57bdd6a96
-- title:
--   Signed Support: gram eq source vertices
-- statement:
--   The Signed Support construction uses the gram eq source vertices property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L54-L59
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L54-L59

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.gram_eq_source_vertices {B : Type*} (F : Family B) (L : ℕ)
    (a b : B) (sa sb : Bool) (i j : ℕ)
    (h : gram (F.path a sa) L i = gram (F.path b sb) L j) :
    SupportComponents.vertex F L a sa i = SupportComponents.vertex F L b sb j := by sorry
