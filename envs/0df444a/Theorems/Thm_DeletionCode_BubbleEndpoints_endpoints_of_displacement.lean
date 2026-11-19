-- Prove2me | Theorems.Thm_DeletionCode_BubbleEndpoints_endpoints_of_displacement
-- name    : DeletionCode.BubbleEndpoints.endpoints_of_displacement
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:23:29.80971+00:00
-- url     : https://prove2.me/theorems/8343079b-c44c-46c9-90ca-b5540d5c1506
-- title:
--   Bubble Endpoints: endpoints of displacement
-- statement:
--   The actual flank mismatches rule out all interior common vertices with
--   the displacement furnished by surviving source positions.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L68-L105
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/BubbleEndpoints.lean#L68-L105

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_EditRigidity
import Definitions.Def_DeletionCode_BubbleEndpoints
set_option autoImplicit true
open DeletionCode DeletionCode.BubbleEndpoints
open Windows HeaderRecovery CatalogueWords SingleEditOrigins

theorem DeletionCode.BubbleEndpoints.endpoints_of_displacement {k : ℕ} (bubble : BubbleWord k)
    (hleft : bubble.left.getLast? = some (!bubble.bit))
    (hright : bubble.right.head? = some (!bubble.bit))
    (a b : ℕ) (_ha : a ≤ windowLength k - bubble.rho + 1)
    (hb : b ≤ windowLength k - bubble.rho)
    (hag : Agree (listLetters bubble.longWord) a
      (listLetters bubble.shortWord) b (windowLength k - 1))
    (hdis : a = b ∨ a = b + 1) :
    (a = 0 ∧ b = 0) ∨
      (a = windowLength k - bubble.rho + 1 ∧ b = windowLength k - bubble.rho) := by sorry
