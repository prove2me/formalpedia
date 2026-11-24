-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_log_zetaR_le_one
-- name    : Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:58:14.642473+00:00
-- url     : https://prove2.me/theorems/f9d48c7e-6a01-4054-b558-4e4cc5bf39f3
-- title:
--   Standard Lattice: log zeta R le one
-- statement:
--   The Standard Lattice construction uses the log zeta R le one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L26-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L26-L32

import Definitions.Def_Formalism_LogVandermondeBounds_VandPlace
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioLowerBoundOfLogVandermondeGap
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

theorem Formalism.LogVandermondeBounds.StandardLattice.log_zetaR_le_one (M : ℕ) (hM : 2 ≤ M) : Real.log (zetaR M) ≤ 1 := by sorry
