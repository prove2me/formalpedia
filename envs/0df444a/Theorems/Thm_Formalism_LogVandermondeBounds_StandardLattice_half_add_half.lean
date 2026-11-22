-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_half_add_half
-- name    : Formalism.LogVandermondeBounds.StandardLattice.half_add_half
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:13.5378+00:00
-- url     : https://prove2.me/theorems/9330775d-c590-445b-8eeb-2da4e51d17b8
-- title:
--   Standard Lattice: half add half
-- statement:
--   The Standard Lattice construction uses the half add half property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L7-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/CardStabilizerVector.lean#L7-L15

import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeVariationUnbounded
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_CardStabilizerVector
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

theorem Formalism.LogVandermondeBounds.StandardLattice.half_add_half (n : ℕ) : n * (n - 1) / 2 + n * (n + 1) / 2 = n * n := by sorry
