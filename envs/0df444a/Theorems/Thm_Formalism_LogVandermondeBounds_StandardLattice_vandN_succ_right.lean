-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vandN_succ_right
-- name    : Formalism.LogVandermondeBounds.StandardLattice.vandN_succ_right
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:38.066123+00:00
-- url     : https://prove2.me/theorems/e8669643-0d36-4bb2-8bf1-d21356446679
-- title:
--   Standard Lattice: vand N succ right
-- statement:
--   The Standard Lattice construction uses the vand N succ right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/VandNSuccRight.lean#L49-L56
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/VandNSuccRight.lean#L49-L56

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

theorem Formalism.LogVandermondeBounds.StandardLattice.vandN_succ_right (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = vandN x N * ∏ i ∈ range N, (x i - x N) := by sorry
