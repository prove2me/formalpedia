-- Prove2me | Theorems.Thm_DeletionCode_EditLocality_local_vertex_sets_disjoint
-- name    : DeletionCode.EditLocality.local_vertex_sets_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:39:44.040591+00:00
-- url     : https://prove2.me/theorems/680db827-35bb-4876-9cc6-e28ae31b967d
-- title:
--   Edit Locality: local vertex sets disjoint
-- statement:
--   The Edit Locality construction uses the local vertex sets disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L87-L100
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L87-L100

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality
set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditLocality.local_vertex_sets_disjoint {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (s p t q : ℕ) (hei : Inside e s p) (hfi : Inside f t q)
    (hsp : s + p ≤ n) (htq : t + q ≤ n)
    (hdis : Disjoint (Set.Ico s (s + p)) (Set.Ico t (t + q))) :
    Disjoint (localVertices e x s p (windowLength k))
      (localVertices f x t q (windowLength k)) := by sorry
