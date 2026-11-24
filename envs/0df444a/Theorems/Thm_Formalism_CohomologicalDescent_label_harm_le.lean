-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_label_harm_le
-- name    : Formalism.CohomologicalDescent.label_harm_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:07.382063+00:00
-- url     : https://prove2.me/theorems/7ea5e302-f4ee-47af-8b92-2466918e95b8
-- title:
--   Cohomological Descent: label harm le
-- statement:
--   The Cohomological Descent construction uses the label harm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L106-L121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L106-L121

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

theorem Formalism.CohomologicalDescent.label_harm_le {l h : ℕ} (hl0 : 0 < l) (hlh : l ≤ 2 * h) :
    ((harmonic (h / l) : ℚ) : ℝ) ≤ 1 + Real.log ((h : ℝ) / (l : ℝ)) := by sorry
