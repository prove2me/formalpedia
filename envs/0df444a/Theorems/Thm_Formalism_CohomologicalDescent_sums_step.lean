-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_sums_step
-- name    : Formalism.CohomologicalDescent.sums_step
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:35:43.763555+00:00
-- url     : https://prove2.me/theorems/d2f4e3ea-617d-4b8c-8dc8-06df82443515
-- title:
--   Cohomological Descent: sums step
-- statement:
--   The Cohomological Descent construction uses the sums step property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L122-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L122-L169

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
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

theorem Formalism.CohomologicalDescent.sums_step (c x0 : ℝ) (hc : 0 < c) (hx0 : 0 < x0) (d : ℕ) (hd : 1 ≤ d) :
    min (c / x0) (c / (d : ℝ)) ≤ sums_G c x0 d - sums_G c x0 ((d : ℝ) - 1) := by sorry
