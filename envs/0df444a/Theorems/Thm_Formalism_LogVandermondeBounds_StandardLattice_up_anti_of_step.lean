-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_anti_of_step
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_anti_of_step
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:14.726351+00:00
-- url     : https://prove2.me/theorems/a53054b1-bb0c-4fde-9b2b-d770a29bfb0b
-- title:
--   Standard Lattice: up anti of step
-- statement:
--   The Standard Lattice construction uses the up anti of step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L7-L15

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_anti_of_step (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → f (i + 1) < f i) :
    ∀ i j, i < j → j < N → f j < f i := by sorry
