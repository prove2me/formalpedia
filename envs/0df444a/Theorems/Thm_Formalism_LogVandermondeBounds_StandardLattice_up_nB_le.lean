-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_nB_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_nB_le
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:04.210399+00:00
-- url     : https://prove2.me/theorems/c3f47dc0-b38b-48fe-8399-b48e4446633f
-- title:
--   Standard Lattice: up n B le
-- statement:
--   The Standard Lattice construction uses the up n B le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L101-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L101-L107

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_UpperPlaceHolds
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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_nB_le (k a c : ℕ) : (nBetween k a c : ℝ) ≤ (c : ℝ) := by sorry
