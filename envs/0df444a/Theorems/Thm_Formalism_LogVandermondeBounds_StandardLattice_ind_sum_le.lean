-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_ind_sum_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.ind_sum_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:20.019266+00:00
-- url     : https://prove2.me/theorems/c3094450-ef00-4976-a751-59c5c984de77
-- title:
--   Standard Lattice: ind sum le
-- statement:
--   The Standard Lattice construction uses the ind sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L64-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L64-L75

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

theorem Formalism.LogVandermondeBounds.StandardLattice.ind_sum_le {N : ℕ} (a0 b0 : Fin N) (L : ℝ) (hL : 0 ≤ L) :
    ∑ a, ∑ b ∈ univ.filter (fun b => a < b), (if a = a0 ∧ b = b0 then L else 0) ≤ L := by sorry
