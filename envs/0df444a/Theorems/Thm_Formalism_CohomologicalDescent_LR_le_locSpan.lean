-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_le_locSpan
-- name    : Formalism.CohomologicalDescent.LR.le_locSpan
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:23:22.382798+00:00
-- url     : https://prove2.me/theorems/7e2934be-e5b1-4918-aacd-b6adce2cdafe
-- title:
--   LR: le loc Span
-- statement:
--   The LR construction uses the le loc Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L125-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L125-L129

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQWordAdj
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrcFockZeroRight
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LR.le_locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) {v : V}
    (hv : v ∈ M) : v ∈ locSpan l hl M := by sorry
