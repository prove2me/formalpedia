-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_ld3Gam_inl
-- name    : Formalism.CohomologicalDescent.LD.ld3Gam_inl
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T23:06:38.69085+00:00
-- url     : https://prove2.me/theorems/b2f29646-a4bc-4bbe-a6fe-6a5800950246
-- title:
--   LD: ld3 Gam inl
-- statement:
--   The LD construction uses the ld3 Gam inl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L330-L335
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L330-L335

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

theorem Formalism.CohomologicalDescent.LD.ld3Gam_inl {r s t : ℕ} (h : s + t = r) (q : Fin s) :
    finSumEquivOfAddEq h (Sum.inl q) = Fin.rev (Fin.castLE (by omega) q) := by sorry
