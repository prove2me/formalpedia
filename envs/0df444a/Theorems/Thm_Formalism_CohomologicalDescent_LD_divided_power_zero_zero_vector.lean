-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_divided_power_zero_zero_vector
-- name    : Formalism.CohomologicalDescent.LD.divided_power_zero_zero_vector
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:40:26.464392+00:00
-- url     : https://prove2.me/theorems/ca8c6081-8fb4-4de5-8d18-64935184cb97
-- title:
--   LD: divided power zero zero vector
-- statement:
--   The LD construction uses the divided power zero zero vector property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L321-L332
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/DividedPowerZeroZeroVector.lean#L321-L332

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

theorem Formalism.CohomologicalDescent.LD.divided_power_zero_zero_vector (w y i k : ℕ) :
    rowDiv ℤ 0 0 k (vec2 w y i) = ((w - y - i + y).choose k : ℤ) • vec2 w y i := by sorry
