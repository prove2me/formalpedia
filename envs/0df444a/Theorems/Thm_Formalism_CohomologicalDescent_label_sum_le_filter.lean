-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_label_sum_le_filter
-- name    : Formalism.CohomologicalDescent.label_sum_le_filter
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:29:42.550827+00:00
-- url     : https://prove2.me/theorems/6a498f38-6ed3-4997-a7f0-6b66aefd43b8
-- title:
--   Cohomological Descent: label sum le filter
-- statement:
--   The Cohomological Descent construction uses the label sum le filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L34-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L34-L42

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

theorem Formalism.CohomologicalDescent.label_sum_le_filter {l : ℕ} (hl : l.Prime) (s : Finset ℤ) (mB : ℤ) (c : ℤ → ℝ)
    (hc : ∀ x ∈ s, 0 ≤ c x) (hr : ∀ x ∈ s, 0 < x - mB ∧ x - mB < (l : ℤ) ^ 2) :
    ∑ x ∈ s, c x * (vl l (x - mB) : ℝ) ≤ ∑ x ∈ s.filter (fun x => (l : ℤ) ∣ x - mB), c x := by sorry
