-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_harm_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.harm_le
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:47.334605+00:00
-- url     : https://prove2.me/theorems/582c07d6-047d-4a19-8708-8fc5e2ba289b
-- title:
--   Standard Lattice: harm le
-- statement:
--   The Standard Lattice construction uses the harm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L95-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L95-L99

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogVandermondeVariationUnbounded
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

theorem Formalism.LogVandermondeBounds.StandardLattice.harm_le (N : ℕ) : ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) ≤ 1 + Real.log N := by sorry
