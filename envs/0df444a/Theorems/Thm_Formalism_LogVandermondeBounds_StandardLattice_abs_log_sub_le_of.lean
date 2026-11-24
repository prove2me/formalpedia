-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_abs_log_sub_le_of
-- name    : Formalism.LogVandermondeBounds.StandardLattice.abs_log_sub_le_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:16:06.505809+00:00
-- url     : https://prove2.me/theorems/b26229ed-2b65-4421-a307-351c78fa681a
-- title:
--   Standard Lattice: abs log sub le of
-- statement:
--   The Standard Lattice construction uses the abs log sub le of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L8-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogVandermondeVariationUnbounded.lean#L8-L28

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

theorem Formalism.LogVandermondeBounds.StandardLattice.abs_log_sub_le_of {x y m e : ℝ} (hm : 0 < m) (hx : m ≤ x) (hy : m ≤ y)
    (hxy : |x - y| ≤ e) : |Real.log x - Real.log y| ≤ e / m := by sorry
