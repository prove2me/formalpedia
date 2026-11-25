-- Prove2me | Theorems.Thm_Bl_FirstBlockLemmaL_goal1
-- name    : Bl.FirstBlockLemmaL.goal1
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T11:16:15.131206+00:00
-- url     : https://prove2.me/theorems/041d5ef8-ae7d-4a85-bbc8-253d8fe7a7dc
-- title:
--   First Block Lemma L: goal1
-- statement:
--   The First Block Lemma L construction uses the goal1 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaL/Imports.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Lemmata/FirstBlockLemmaL/Imports.lean#L5-L19

import Mathlib
import Definitions.Def_Lemmata_FirstBlockLemmaL_Imports
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Bl Bl.FirstBlockLemmaL

theorem Bl.FirstBlockLemmaL.goal1 :
  ∀ (ℓ : Nat) [Fact (Nat.Prime ℓ)] (s : Multiset.{0} Nat),
  (∀ (x : Nat), Membership.mem.{0, 0} s x → Ne.{1} x 0) →
    Eq.{1} (padicValNat ℓ (Multiset.prod.{0} s)) (Multiset.sum.{0} (Multiset.map.{0, 0} (padicValNat ℓ) s)) := by sorry
