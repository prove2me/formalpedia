-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_rule_support_iff
-- name    : DeletionCode.SignedSupport.rule_support_iff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:08:04.657678+00:00
-- url     : https://prove2.me/theorems/7354b2fc-05df-4cac-9903-d72fe6fa1bad
-- title:
--   Signed Support: rule support iff
-- statement:
--   The Signed Support construction uses the rule support iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L233-L249
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L233-L249

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.rule_support_iff {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (g : Gram L) :
    ruleSpectrum F L S g ≠ 0 ↔ ∃ b ∈ S, HasGram F L b g := by sorry
