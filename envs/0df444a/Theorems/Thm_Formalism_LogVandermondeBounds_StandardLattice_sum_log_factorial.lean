-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_sum_log_factorial
-- name    : Formalism.LogVandermondeBounds.StandardLattice.sum_log_factorial
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:53:27.683826+00:00
-- url     : https://prove2.me/theorems/9512f0b7-8149-4f1e-afab-1760758671b7
-- title:
--   Standard Lattice: sum log factorial
-- statement:
--   The Standard Lattice construction uses the sum log factorial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L34-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioLowerBoundOfLogVandermondeGap.lean#L34-L43

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

theorem Formalism.LogVandermondeBounds.StandardLattice.sum_log_factorial (k r : ℕ) (hkr : k ≤ r) :
    ∑ M ∈ Ico (k + 1) (r + 1), Real.log (((M - 1).factorial : ℕ) : ℝ)
      + ∑ i ∈ range k, Real.log ((i.factorial : ℕ) : ℝ)
      = ∑ i ∈ range r, Real.log ((i.factorial : ℕ) : ℝ) := by sorry
