-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_two_mul_card_lt_pairs
-- name    : Formalism.LogVandermondeBounds.StandardLattice.two_mul_card_lt_pairs
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:15.863473+00:00
-- url     : https://prove2.me/theorems/f33cd742-5e52-4eb6-9536-c25a0c709461
-- title:
--   Standard Lattice: two mul card lt pairs
-- statement:
--   The Standard Lattice construction uses the two mul card lt pairs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L7-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/BlockDimensionIdentities.lean#L7-L16

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_BlockDimensionIdentities
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LogVandermondeBounds Formalism.LogVandermondeBounds.StandardLattice
open Finset

theorem Formalism.LogVandermondeBounds.StandardLattice.two_mul_card_lt_pairs (n : ℕ) :
    2 * ((range n ×ˢ range n).filter (fun p : ℕ × ℕ => p.1 < p.2)).card = n * (n - 1) := by sorry
