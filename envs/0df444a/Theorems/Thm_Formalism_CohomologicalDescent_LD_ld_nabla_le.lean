-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld_nabla_le
-- name    : Formalism.CohomologicalDescent.LD.ld_nabla_le
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:40:53.997455+00:00
-- url     : https://prove2.me/theorems/4c06e7db-7228-41e9-a4c0-1a63d49cb5fc
-- title:
--   LD: ld nabla le
-- statement:
--   The LD construction uses the ld nabla le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L410-L425
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L410-L425

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

theorem Formalism.CohomologicalDescent.LD.ld_nabla_le (w y : ℕ) (hy : y ≤ w) :
    dualWeyl ℤ 2 2 (wt2 w y) ≤ Submodule.span ℤ {v | ∃ j, y + j ≤ w ∧ v = vec2 w y j} := by sorry
