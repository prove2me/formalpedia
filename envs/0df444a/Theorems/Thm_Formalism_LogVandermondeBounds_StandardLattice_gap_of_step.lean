-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_gap_of_step
-- name    : Formalism.LogVandermondeBounds.StandardLattice.gap_of_step
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:54.996869+00:00
-- url     : https://prove2.me/theorems/de3d58b4-5673-4107-ac6d-c9fa8403398c
-- title:
--   Standard Lattice: gap of step
-- statement:
--   The Standard Lattice construction uses the gap of step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/VandNSuccRight.lean#L17-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/VandNSuccRight.lean#L17-L27

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_VandNSuccRight
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

theorem Formalism.LogVandermondeBounds.StandardLattice.gap_of_step (f : ℕ → ℝ) (N : ℕ) (h : ∀ i, i + 1 < N → 1 ≤ f (i + 1) - f i) :
    ∀ i j, i < j → j < N → 1 ≤ f j - f i := by sorry
