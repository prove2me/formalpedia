-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_gram_eq_iff_agree
-- name    : DeletionCode.SignedSupport.gram_eq_iff_agree
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:10:56.830035+00:00
-- url     : https://prove2.me/theorems/87e09e74-97d4-40b8-8653-444e1008702e
-- title:
--   Signed Support: gram eq iff agree
-- statement:
--   The Signed Support construction uses the gram eq iff agree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L45-L52
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L45-L52

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.gram_eq_iff_agree (p q : Letters) (L i j : ℕ) :
    gram p L i = gram q L j ↔ Agree p i q j L := by sorry
