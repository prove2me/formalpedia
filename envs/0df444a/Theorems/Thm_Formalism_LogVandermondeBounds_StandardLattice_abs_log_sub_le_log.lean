-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_abs_log_sub_le_log
-- name    : Formalism.LogVandermondeBounds.StandardLattice.abs_log_sub_le_log
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T09:52:29.553066+00:00
-- url     : https://prove2.me/theorems/32b8c823-f22d-4f56-b920-133bee85d0c8
-- title:
--   Standard Lattice: abs log sub le log
-- statement:
--   The Standard Lattice construction uses the abs log sub le log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L30-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L30-L44

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

theorem Formalism.LogVandermondeBounds.StandardLattice.abs_log_sub_le_log {x y e : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hxy : |x - y| ≤ e) :
    |Real.log x - Real.log y| ≤ Real.log (1 + e) := by sorry
