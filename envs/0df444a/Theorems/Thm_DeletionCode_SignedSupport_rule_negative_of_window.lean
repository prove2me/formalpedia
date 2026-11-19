-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_rule_negative_of_window
-- name    : DeletionCode.SignedSupport.rule_negative_of_window
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:15:11.317205+00:00
-- url     : https://prove2.me/theorems/379d3c4f-203b-4cd7-8f2c-7aa7dc2f1cad
-- title:
--   Signed Support: rule negative of window
-- statement:
--   The Signed Support construction uses the rule negative of window property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L225-L231
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L225-L231

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.rule_negative_of_window {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (b : B) (hb : b ∈ S) (g : Gram L)
    (hg : g ∈ windowSet (F.path b false) L (F.extra b false)) :
    ruleSpectrum F L S g = -1 := by sorry
