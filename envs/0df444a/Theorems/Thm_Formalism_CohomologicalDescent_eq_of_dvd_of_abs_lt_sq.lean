-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_eq_of_dvd_of_abs_lt_sq
-- name    : Formalism.CohomologicalDescent.eq_of_dvd_of_abs_lt_sq
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:30:05.824259+00:00
-- url     : https://prove2.me/theorems/cbe14952-7c0d-4a96-8f4e-e28494f949aa
-- title:
--   Cohomological Descent: eq of dvd of abs lt sq
-- statement:
--   The Cohomological Descent construction uses the eq of dvd of abs lt sq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LogarithmEquivalence.lean#L12-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LogarithmEquivalence.lean#L12-L27

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_ContentDistanceBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LogarithmEquivalence
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical

theorem Formalism.CohomologicalDescent.eq_of_dvd_of_abs_lt_sq {L : ℝ} (hL : 0 ≤ L) {n : ℤ} (hn : n ≠ 0) (hnL : ((|n| : ℤ) : ℝ) < L ^ 2)
    {l l' : ℕ} (hl : l.Prime) (hl' : l'.Prime) (hLl : L < (l : ℝ)) (hLl' : L < (l' : ℝ))
    (hd : (l : ℤ) ∣ n) (hd' : (l' : ℤ) ∣ n) : l = l' := by sorry
