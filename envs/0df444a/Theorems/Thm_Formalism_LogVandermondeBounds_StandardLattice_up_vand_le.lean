-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_up_vand_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.up_vand_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:25.111625+00:00
-- url     : https://prove2.me/theorems/31f00907-bd83-41ba-83a3-0ed71002db58
-- title:
--   Standard Lattice: up vand le
-- statement:
--   The Standard Lattice construction uses the up vand le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L40-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/UpperPlaceHolds.lean#L40-L87

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

theorem Formalism.LogVandermondeBounds.StandardLattice.up_vand_le (K : ℕ) (u v : ℕ → ℝ) (hint : ∀ i, i < K → v i < u i ∧ u (i + 1) < v i)
    (hu : ∀ i j, i < j → j < K + 1 → 1 ≤ u i - u j)
    (hv : ∀ i j, i < j → j < K → v j < v i) : vandN v K ≤ vandN u (K + 1) := by sorry
