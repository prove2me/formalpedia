-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_nB_zero
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_nB_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:25.0066+00:00
-- url     : https://prove2.me/theorems/d32a4387-2f05-45ee-8607-3ab0749476c9
-- title:
--   Standard Lattice: up n B zero
-- statement:
--   The Standard Lattice construction uses the up n B zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L93-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L93-L99

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_nB_zero (n a c : ℕ) (hac : a < c) (hc : c < n + 1) : nBetween (n + 2) a c = 0 := by sorry
