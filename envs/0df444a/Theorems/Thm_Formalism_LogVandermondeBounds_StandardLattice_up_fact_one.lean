-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_fact_one
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_fact_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:20.09346+00:00
-- url     : https://prove2.me/theorems/6453b4a2-8214-4ae2-a142-f9c3e1cb12dc
-- title:
--   Standard Lattice: up fact one
-- statement:
--   The Standard Lattice construction uses the up fact one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L231-L238
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L231-L238

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_fact_one (N : ℕ) : 1 ≤ ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) := by sorry
