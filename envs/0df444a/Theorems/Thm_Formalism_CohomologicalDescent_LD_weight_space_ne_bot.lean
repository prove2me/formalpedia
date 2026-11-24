-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_weight_space_ne_bot
-- name    : Formalism.CohomologicalDescent.LD.weight_space_ne_bot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:07:27.070879+00:00
-- url     : https://prove2.me/theorems/7a19c62f-63be-4853-b928-4c31cd059aa1
-- title:
--   LD: weight space ne bot
-- statement:
--   The LD construction uses the weight space ne bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L229-L233
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L229-L233

import Definitions.Def_Formalism_PieriBlockIdeals_LastGradedOfGradedAlone
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LastGradedImpliesOneBlock
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LEhwLemmas
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightProdLeadingMinors
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
open Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LA

theorem Formalism.CohomologicalDescent.LD.weight_space_ne_bot {r : ℕ} {ν μ : Fin r → ℕ} {x : MvPolynomial (Fin r × Fin r) ℤ} (hx : x ∈ nablaWt r ν μ)
    (hne : x ≠ 0) : nablaWt r ν μ ≠ ⊥ := by sorry
