-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_inner_harm_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.inner_harm_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:40.189798+00:00
-- url     : https://prove2.me/theorems/d66291cb-e00d-4ade-858f-8a9945366dc5
-- title:
--   Standard Lattice: inner harm le
-- statement:
--   The Standard Lattice construction uses the inner harm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L77-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L77-L93

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

theorem Formalism.LogVandermondeBounds.StandardLattice.inner_harm_le {N : ℕ} (a : Fin N) :
    ∑ b ∈ univ.filter (fun b => a < b), (1 : ℝ) / (((b.val - a.val - 1 : ℕ) : ℝ) + 1) ≤
      ∑ i ∈ range N, (1 : ℝ) / ((i : ℝ) + 1) := by sorry
