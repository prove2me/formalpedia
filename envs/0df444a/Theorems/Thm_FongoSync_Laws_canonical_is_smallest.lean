-- Prove2me | Theorems.Thm_FongoSync_Laws_canonical_is_smallest
-- name    : FongoSync.Laws.canonical_is_smallest
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T08:06:34.95114+00:00
-- url     : https://prove2.me/theorems/49c21c5b-36dc-4b7e-9d76-82560c48af2e
-- title:
--   Laws: canonical is smallest
-- statement:
--   Each gid's canonical gid is the smallest gid in its group.
--
--   Source: https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L127-L129
-- source:
--   https://github.com/bongofongo/fongo-sync/blob/7e3f771e7c150a69dbbd87827b7ffe4525f219a7/FongoSync/Laws.lean#L127-L129

import Definitions.Def_FongoSync_Examples
import Definitions.Def_FongoSync_Model
import Definitions.Def_FongoSync_Run
import Definitions.Def_FongoSync_Laws
set_option autoImplicit false
open FongoSync FongoSync.Laws
open FongoSync

theorem FongoSync.Laws.canonical_is_smallest (E : List Edge) (g : Gid) :
    Connected E g (canonical E g) ∧ ∀ h, Connected E g h → canonical E g ≤ h := by sorry
