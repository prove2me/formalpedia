-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_WorkedExample_image_Icc_neg_shift
-- name    : Formalism.CohomologicalDescent.WorkedExample.image_Icc_neg_shift
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:01:42.858284+00:00
-- url     : https://prove2.me/theorems/1f0ccba9-94fc-4dc5-9df6-d66c13f18aad
-- title:
--   Worked Example: image Icc neg shift
-- statement:
--   The Worked Example construction uses the image Icc neg shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/WorkedExample.lean#L18-L26

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_MultiplicityZeroThickEmbedding
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ParameterBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_WorkedExample
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.WorkedExample
open Formalism.CohomologicalDescent

theorem Formalism.CohomologicalDescent.WorkedExample.image_Icc_neg_shift (h x y : ℤ) :
    (Finset.Icc x y).image (fun u => h - u) = Finset.Icc (h - y) (h - x) := by sorry
