-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_rule_support_eq_edge_union
-- name    : DeletionCode.SignedSupport.rule_support_eq_edge_union
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:03:32.927426+00:00
-- url     : https://prove2.me/theorems/b445136c-1232-43b4-aeb3-c462696e4209
-- title:
--   Signed Support: rule support eq edge union
-- statement:
--   The signed support is exactly the union of actual windows, without cancellation.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L252-L256
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L252-L256

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.rule_support_eq_edge_union {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S) :
    {g | ruleSpectrum F L S g ≠ 0} = {g | ∃ b ∈ S, HasGram F L b g} := by sorry
