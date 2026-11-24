-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_zero_one_vector
-- name    : Formalism.CohomologicalDescent.LD.divided_power_zero_one_vector
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:28.288491+00:00
-- url     : https://prove2.me/theorems/5dd42ece-5aab-4306-a850-7417e56c6d5d
-- title:
--   LD: divided power zero one vector
-- statement:
--   The LD construction uses the divided power zero one vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L304-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L304-L319

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

theorem Formalism.CohomologicalDescent.LD.divided_power_zero_one_vector (w y i k : ℕ) (h : y + i ≤ w) :
    rowDiv ℤ 0 1 k (vec2 w y i) = (i.choose k : ℤ) • vec2 w y (i - k) := by sorry
