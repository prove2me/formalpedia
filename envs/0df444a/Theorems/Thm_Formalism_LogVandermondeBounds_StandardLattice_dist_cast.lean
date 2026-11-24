-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_dist_cast
-- name    : Formalism.LogVandermondeBounds.StandardLattice.dist_cast
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:58.254707+00:00
-- url     : https://prove2.me/theorems/f9f75452-f67f-4407-b167-9c1290efdeb2
-- title:
--   Standard Lattice: dist cast
-- statement:
--   The Standard Lattice construction uses the dist cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L101-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L101-L106

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

theorem Formalism.LogVandermondeBounds.StandardLattice.dist_cast {N : ℕ} (a b : Fin N) (h : a < b) :
    ((b.val - a.val - 1 : ℕ) : ℝ) + 1 = (b.val : ℝ) - a.val := by sorry
