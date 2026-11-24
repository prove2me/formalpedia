-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_label_card_le
-- name    : Formalism.CohomologicalDescent.label_card_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:03.971669+00:00
-- url     : https://prove2.me/theorems/02437436-7db6-49bf-936d-d44d6086ed71
-- title:
--   Cohomological Descent: label card le
-- statement:
--   The Cohomological Descent construction uses the label card le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L44-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L44-L85

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

theorem Formalism.CohomologicalDescent.label_card_le {l : ℕ} (hl0 : 0 < l) (xm xp mB : ℤ) (hx : xm ≤ xp) :
    ((((Finset.Icc xm xp).filter (fun x => (l : ℤ) ∣ x - mB)).card : ℕ) : ℝ)
      ≤ ((xp - xm : ℤ) : ℝ) / l + 1 := by sorry
