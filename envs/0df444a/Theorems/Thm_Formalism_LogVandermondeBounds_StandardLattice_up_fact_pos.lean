-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_fact_pos
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_fact_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:40:12.679461+00:00
-- url     : https://prove2.me/theorems/a165ff46-a0e3-4a1d-be86-27b8d23a48ab
-- title:
--   Standard Lattice: up fact pos
-- statement:
--   The Standard Lattice construction uses the up fact pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L211-L214
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L211-L214

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_fact_pos (N : ℕ) : 0 < ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := by sorry
