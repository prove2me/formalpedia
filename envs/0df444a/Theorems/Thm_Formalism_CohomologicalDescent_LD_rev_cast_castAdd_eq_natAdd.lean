-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_rev_cast_castAdd_eq_natAdd
-- name    : Formalism.CohomologicalDescent.LD.rev_cast_castAdd_eq_natAdd
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:01.109223+00:00
-- url     : https://prove2.me/theorems/3f62030a-6276-4181-9f04-6bb0474daa43
-- title:
--   LD: rev cast cast Add eq nat Add
-- statement:
--   The LD construction uses the rev cast cast Add eq nat Add property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L21-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L21-L26

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

theorem Formalism.CohomologicalDescent.LD.rev_cast_castAdd_eq_natAdd (p q : ℕ) (a : Fin p) :
    Fin.rev (Fin.cast (Nat.add_comm p q) (Fin.castAdd q a)) = Fin.natAdd q (Fin.rev a) := by sorry
