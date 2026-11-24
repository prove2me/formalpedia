-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_mem
-- name    : Formalism.CohomologicalDescent.leastCongruentPos_mem
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:29:59.741163+00:00
-- url     : https://prove2.me/theorems/7a402c6b-41f9-453b-b43f-61d51222b196
-- title:
--   Cohomological Descent: least Congruent Pos mem
-- statement:
--   The Cohomological Descent construction uses the least Congruent Pos mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L87-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L87-L100

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LabelSumNeedsLeFalse
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

theorem Formalism.CohomologicalDescent.leastCongruentPos_mem {l : ℕ} (hl : 0 < l) (D : ℤ) (hD : 0 ≤ D) :
    1 ≤ d0 l D ∧ (l : ℤ) ∣ D - (d0 l D : ℤ) := by sorry
