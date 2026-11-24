-- Prove2me | Theorems.Thm_Formalism_LogVandermondeBounds_StandardLattice_log_fact_le
-- name    : Formalism.LogVandermondeBounds.StandardLattice.log_fact_le
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T09:52:34.652915+00:00
-- url     : https://prove2.me/theorems/6f9102b9-b42a-430f-a14b-8cd46cdba91e
-- title:
--   Standard Lattice: log fact le
-- statement:
--   The Standard Lattice construction uses the log fact le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioUpperBoundOfUpperPlace.lean#L27-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogVandermondeBounds/LogVandermondeProofs/LogRatioUpperBoundOfUpperPlace.lean#L27-L36

import Definitions.Def_Formalism_LogVandermondeBounds_UpperPlace
import Mathlib
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_LogRatioUpperBoundOfUpperPlace
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

theorem Formalism.LogVandermondeBounds.StandardLattice.log_fact_le {M k : ℕ} (hM : M - 1 ≤ 2 * k) (hk : 1 ≤ k) :
    Real.log (((M - 1).factorial : ℕ) : ℝ) ≤ 2 * k * Real.log (2 * k) := by sorry
