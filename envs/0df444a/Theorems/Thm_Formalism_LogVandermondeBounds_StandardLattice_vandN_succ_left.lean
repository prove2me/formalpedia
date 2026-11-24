-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_vandN_succ_left
-- name    : Formalism.LogVandermondeBounds.StandardLattice.vandN_succ_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:14:24.42002+00:00
-- url     : https://prove2.me/theorems/12700609-a85e-40a6-8cd9-ca5cee40af02
-- title:
--   Standard Lattice: vand N succ left
-- statement:
--   The Standard Lattice construction uses the vand N succ left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/VandNSuccRight.lean#L58-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/VandNSuccRight.lean#L58-L65

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

theorem Formalism.LogVandermondeBounds.StandardLattice.vandN_succ_left (x : ℕ → ℝ) (N : ℕ) :
    vandN x (N + 1) = (∏ j ∈ Ico 1 (N + 1), (x 0 - x j)) * vandN (fun i => x (i + 1)) N := by sorry
