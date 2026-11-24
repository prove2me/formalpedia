-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_symmetric_block_weight_zero
-- name    : Formalism.CohomologicalDescent.LD.symmetric_block_weight_zero
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T22:41:08.32834+00:00
-- url     : https://prove2.me/theorems/ceb1b982-60d2-433c-a236-c1f8de35f9f0
-- title:
--   LD: symmetric block weight zero
-- statement:
--   The LD construction uses the symmetric block weight zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L804-L805
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L804-L805

import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LD
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LD.symmetric_block_weight_zero (q w : ℕ) : blockWt 1 q w (fun _ => 0) (ldZ q) = w := by sorry
