-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_adjugate_entry_weighted_homog
-- name    : Formalism.CohomologicalDescent.LD.adjugate_entry_weighted_homog
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:06:17.425796+00:00
-- url     : https://prove2.me/theorems/367e4e30-acf4-41f8-9715-0d56f9a7df55
-- title:
--   LD: adjugate entry weighted homog
-- statement:
--   The LD construction uses the adjugate entry weighted homog property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L497-L524
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L497-L524

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

theorem Formalism.CohomologicalDescent.LD.adjugate_entry_weighted_homog (r : ℕ) (i j : Fin r) :
    IsWeightedHomogeneous (rowW r r) ((genericMatrix' ℤ r).adjugate i j) (fun c => if c = j then 0 else 1) := by sorry
