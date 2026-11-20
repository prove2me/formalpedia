-- Prove2me | Theorems.Thm_DeletionCode_TwoEditWindows_avoids_later_of_not_avoids
-- name    : DeletionCode.TwoEditWindows.avoids_later_of_not_avoids
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:28:52.371841+00:00
-- url     : https://prove2.me/theorems/ad21a9ff-f3d6-48b2-b017-55b3814e30bb
-- title:
--   Two Edit Windows: avoids later of not avoids
-- statement:
--   If an edit obstructs one block, every later disjoint block avoids it.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L17-L22
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/TwoEditWindows.lean#L17-L22

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows
set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows

theorem DeletionCode.TwoEditWindows.avoids_later_of_not_avoids {k start next edit : ℕ}
    (hgap : start + k ≤ next) (hbad : ¬ Avoids k start edit) :
    Avoids k next edit := by sorry
