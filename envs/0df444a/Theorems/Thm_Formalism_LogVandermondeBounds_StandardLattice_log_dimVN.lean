-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_log_dimVN
-- name    : Formalism.LogVandermondeBounds.StandardLattice.log_dimVN
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:37.379798+00:00
-- url     : https://prove2.me/theorems/c8492cc1-1176-4464-a77f-32f57d97b95d
-- title:
--   Standard Lattice: log dim VN
-- statement:
--   The Standard Lattice construction uses the log dim VN property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L45-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L45-L51

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

theorem Formalism.LogVandermondeBounds.StandardLattice.log_dimVN (x : ℕ → ℝ) (N : ℕ) (h : 0 < vandN x N) :
    0 < dimVN x N ∧ Real.log (dimVN x N)
      = Real.log (vandN x N) - ∑ i ∈ range N, Real.log ((i.factorial : ℕ) : ℝ) := by sorry
