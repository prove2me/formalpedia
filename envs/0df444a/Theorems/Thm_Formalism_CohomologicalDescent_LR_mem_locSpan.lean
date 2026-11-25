-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_mem_locSpan
-- name    : Formalism.CohomologicalDescent.LR.mem_locSpan
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:33:34.546189+00:00
-- url     : https://prove2.me/theorems/0ba0e571-e6b9-5f5a-a191-6112851f1a15
-- title:
--   LR: mem loc Span
-- statement:
--   The LR construction uses the mem loc Span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L122-L123
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L122-L123

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

theorem Formalism.CohomologicalDescent.LR.mem_locSpan (l : ℕ) (hl : l.Prime) {V : Type*} [AddCommGroup V] [Module ℚ V] (M : AddSubgroup V) (v : V) :
    v ∈ locSpan l hl M ↔ ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ m • v ∈ M := by sorry
