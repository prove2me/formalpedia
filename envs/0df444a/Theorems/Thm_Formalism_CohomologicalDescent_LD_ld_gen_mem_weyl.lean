-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_gen_mem_weyl
-- name    : Formalism.CohomologicalDescent.LD.ld_gen_mem_weyl
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:41:10.39983+00:00
-- url     : https://prove2.me/theorems/382b14a2-e71f-4a9e-b938-4ef743f05526
-- title:
--   LD: ld gen mem weyl
-- statement:
--   The LD construction uses the ld gen mem weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L527-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L527-L533

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

theorem Formalism.CohomologicalDescent.LD.ld_gen_mem_weyl (w y j : ℕ) :
    ((w - y).choose j : ℤ) • vec2 w y j ∈ weyl ℤ 2 2 le_rfl (wt2 w y) := by sorry
