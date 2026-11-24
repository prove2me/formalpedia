-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_four_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_four_le
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:22.216551+00:00
-- url     : https://prove2.me/theorems/d80a1ab0-c83e-455a-8185-74e0dcc6ca64
-- title:
--   Standard Lattice: up four le
-- statement:
--   The Standard Lattice construction uses the up four le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L240-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L240-L243

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_four_le (n t : ℕ) (ht : 1 ≤ t) : (4 : ℝ) ≤ ((n : ℝ) + 2) * ((t : ℝ) + t) := by sorry
