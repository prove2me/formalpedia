-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_dual_weight_total
-- name    : Formalism.CohomologicalDescent.LD.dual_weight_total
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:06:28.03888+00:00
-- url     : https://prove2.me/theorems/4019dbb4-7f09-474a-aef3-c5f44de9b8ed
-- title:
--   LD: dual weight total
-- statement:
--   The LD construction uses the dual weight total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L1000-L1004
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L1000-L1004

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

theorem Formalism.CohomologicalDescent.LD.dual_weight_total {r : ℕ} (M : ℕ) (ν : Fin r → ℕ) (hM : ∀ a, ν a ≤ M) :
    ∑ a, dualWt M ν a + ∑ a, ν a = r * M := by sorry
