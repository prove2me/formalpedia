-- Prove2me | Theorems.Thm_DeletionCode_EditLocality_local_windows_ne
-- name    : DeletionCode.EditLocality.local_windows_ne
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:39:32.570105+00:00
-- url     : https://prove2.me/theorems/1c297803-b864-4cf2-930a-4059fc91406c
-- title:
--   Edit Locality: local windows ne
-- statement:
--   No equal (L-1)-windows arise from changes in disjoint source intervals.
--   This includes either side of either local replacement, by using unchanged
--   as the edit for a path lying in the original word.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L60-L79
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/EditLocality.lean#L60-L79

import Definitions.Def_DeletionCode_EditRigidity
import Mathlib.Order.Interval.Set.Basic
import Definitions.Def_DeletionCode_EditLocality
set_option autoImplicit true
open DeletionCode DeletionCode.EditLocality
open Windows HeaderRecovery SingleEditOrigins

theorem DeletionCode.EditLocality.local_windows_ne {n k : ℕ} (hk : 1 ≤ k) (x : Letters)
    (hx : KUnique x n k) (e f : Edit) (he : e.Valid n) (hf : f.Valid n)
    (s p t q : ℕ) (hei : Inside e s p) (hfi : Inside f t q)
    (hsp : s + p ≤ n) (htq : t + q ≤ n)
    (hdis : Disjoint (Set.Ico s (s + p)) (Set.Ico t (t + q)))
    (a b : ℕ) (ha : s ≤ a) (hb : t ≤ b)
    (haend : a + (windowLength k - 1) ≤ s + e.outputLength p)
    (hbend : b + (windowLength k - 1) ≤ t + f.outputLength q) :
    ¬ Agree (e.word x) a (f.word x) b (windowLength k - 1) := by sorry
