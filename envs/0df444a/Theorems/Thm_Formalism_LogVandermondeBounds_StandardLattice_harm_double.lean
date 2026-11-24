-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_harm_double
-- name    : Formalism.LogVandermondeBounds.StandardLattice.harm_double
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T09:52:31.040101+00:00
-- url     : https://prove2.me/theorems/b66195cf-83d1-4365-9433-12cc00da206d
-- title:
--   Standard Lattice: harm double
-- statement:
--   The Standard Lattice construction uses the harm double property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L221-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L221-L233

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

theorem Formalism.LogVandermondeBounds.StandardLattice.harm_double (N : ℕ) :
    ∑ a : Fin N, ∑ b ∈ univ.filter (fun b => a < b), 2 / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) ≤
      2 * N * (1 + Real.log N) := by sorry
