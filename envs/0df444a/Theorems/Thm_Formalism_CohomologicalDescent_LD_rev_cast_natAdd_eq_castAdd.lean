-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_rev_cast_natAdd_eq_castAdd
-- name    : Formalism.CohomologicalDescent.LD.rev_cast_natAdd_eq_castAdd
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T23:05:55.648744+00:00
-- url     : https://prove2.me/theorems/6bd14573-0c15-4af7-81de-b56c4c5384c4
-- title:
--   LD: rev cast nat Add eq cast Add
-- statement:
--   The LD construction uses the rev cast nat Add eq cast Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L28-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L28-L33

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

theorem Formalism.CohomologicalDescent.LD.rev_cast_natAdd_eq_castAdd (p q : ℕ) (a : Fin q) :
    Fin.rev (Fin.cast (Nat.add_comm p q) (Fin.natAdd p a)) = Fin.castAdd p (Fin.rev a) := by sorry
