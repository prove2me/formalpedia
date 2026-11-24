-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_weight_wc_eq_degree
-- name    : Formalism.CohomologicalDescent.LD.weight_wc_eq_degree
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:44.061897+00:00
-- url     : https://prove2.me/theorems/53640509-1b6a-49e4-bafb-783c9e7ee3ac
-- title:
--   LD: weight wc eq degree
-- statement:
--   The LD construction uses the weight wc eq degree property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L691-L696
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L691-L696

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

theorem Formalism.CohomologicalDescent.LD.weight_wc_eq_degree {r : ℕ} (c : Fin r) (d : Fin r × Fin r →₀ ℕ) :
    Finsupp.weight (columnWeight c) d = ((Finsupp.weight (rowW r r) d c : ℕ) : ℤ) := by sorry
