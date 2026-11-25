-- Prove2me | Theorems.Thm_Formalism_BehrendSets_Ord_card_units
-- name    : Formalism.BehrendSets.Ord.card_units
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:20:13.586401+00:00
-- url     : https://prove2.me/theorems/2cc16d9a-d492-47b7-9a1f-8cfc88e6abd6
-- title:
--   Ord: card units
-- statement:
--   The Ord construction uses the card units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoPowDvdPowTwoPowSubOne.lean#L7-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/BehrendSets/BehrendVariance/TwoPowDvdPowTwoPowSubOne.lean#L7-L10

import Definitions.Def_Formalism_BehrendSets_Statement
import Definitions.Def_Formalism_BehrendSets_BehrendVariance_TwoPowDvdPowTwoPowSubOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open Formalism Formalism.BehrendSets Formalism.BehrendSets.Ord

theorem Formalism.BehrendSets.Ord.card_units (s : ℕ) : Nat.card (ZMod (2 ^ (s + 2)))ˣ = 2 ^ (s + 1) := by sorry
