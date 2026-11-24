-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_label_second
-- name    : Formalism.CohomologicalDescent.label_second
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:30:10.392463+00:00
-- url     : https://prove2.me/theorems/32f30b88-9332-4c78-9ca8-b9d75f6cacd1
-- title:
--   Cohomological Descent: label second
-- statement:
--   The Cohomological Descent construction uses the label second property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L130-L254
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LabelSumNeedsLeFalse.lean#L130-L254

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

theorem Formalism.CohomologicalDescent.label_second {l k t h : ℕ} {i : ℝ} {xm mB : ℤ} (hl : l.Prime) (hi : 0 ≤ i)
    (hmB : 0 ≤ mB) (hmx : mB < xm) (hxh : xm ≤ (h : ℤ)) (hh : h < l ^ 2) (hlh : l ≤ 2 * h) :
    ∑ ct ∈ Finset.Ioo mB xm,
      min (min (k : ℝ) (t : ℝ)) (i / ((xm - ct : ℤ) : ℝ)) * (vl l (ct - mB) : ℝ)
    ≤ (if ((d0 l (xm - mB) : ℕ) : ℤ) < xm - mB then
        min (min (k : ℝ) (t : ℝ)) (i / (d0 l (xm - mB) : ℝ)) else 0) +
      (i / (l : ℝ)) * (1 + Real.log ((h : ℝ) / (l : ℝ))) := by sorry
