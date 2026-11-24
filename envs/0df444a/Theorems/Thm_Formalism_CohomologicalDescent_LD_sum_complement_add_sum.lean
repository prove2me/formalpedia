-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_sum_complement_add_sum
-- name    : Formalism.CohomologicalDescent.LD.sum_complement_add_sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:14.042353+00:00
-- url     : https://prove2.me/theorems/2d336a58-397d-43eb-8550-94d60be641b9
-- title:
--   LD: sum complement add sum
-- statement:
--   The LD construction uses the sum complement add sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L42-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L42-L45

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

theorem Formalism.CohomologicalDescent.LD.sum_complement_add_sum {p : ℕ} (M : ℕ) (f : Fin p → ℕ) (hf : ∀ a, f a ≤ M) :
    ∑ a, (M - f a) + ∑ a, f a = p * M := by sorry
