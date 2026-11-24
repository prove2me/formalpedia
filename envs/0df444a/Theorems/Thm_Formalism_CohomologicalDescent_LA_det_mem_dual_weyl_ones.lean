-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mem_dual_weyl_ones
-- name    : Formalism.CohomologicalDescent.LA.det_mem_dual_weyl_ones
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:33.045451+00:00
-- url     : https://prove2.me/theorems/b88de171-6b99-4fab-beb9-3cdb091aa6fe
-- title:
--   LA: det mem dual weyl ones
-- statement:
--   The LA construction uses the det mem dual weyl ones property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L209-L243
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L209-L243

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LA.det_mem_dual_weyl_ones (r : ℕ) : genericDet ℤ r ∈ dualWeyl ℤ r r (fun _ => 1) := by sorry
