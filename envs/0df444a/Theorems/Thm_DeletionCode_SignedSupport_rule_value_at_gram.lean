-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_rule_value_at_gram
-- name    : DeletionCode.SignedSupport.rule_value_at_gram
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:10:30.528538+00:00
-- url     : https://prove2.me/theorems/cbe36936-b2de-43f2-af49-018586ab364b
-- title:
--   Signed Support: rule value at gram
-- statement:
--   Every gram in a bubble retains that bubble's coefficient in the whole rule.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L211-L223
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L211-L223

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.rule_value_at_gram {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (S : Finset B) (hdis : VertexDisjointOn F L S)
    (b : B) (hb : b ∈ S) (g : Gram L) (hg : HasGram F L b g) :
    ruleSpectrum F L S g = bubbleSpectrum F L b g := by sorry
