-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_fact_mono
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_fact_mono
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T09:53:20.077848+00:00
-- url     : https://prove2.me/theorems/6f6c0c3e-9e46-43cc-bc6f-4a9b4a304186
-- title:
--   Standard Lattice: up fact mono
-- statement:
--   The Standard Lattice construction uses the up fact mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L216-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L216-L226

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_fact_mono (N P : ℕ) (h : N ≤ P) :
    ∏ i ∈ range N, ((i.factorial : ℕ) : ℝ) ≤ ∏ i ∈ range P, ((i.factorial : ℕ) : ℝ) := by sorry
