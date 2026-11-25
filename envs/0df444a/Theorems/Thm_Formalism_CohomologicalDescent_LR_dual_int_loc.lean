-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_dual_int_loc
-- name    : Formalism.CohomologicalDescent.LR.dual_int_loc
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T11:24:09.861637+00:00
-- url     : https://prove2.me/theorems/412b07ab-b098-445d-8c15-509dace2c729
-- title:
--   LR: dual int loc
-- statement:
--   The LR construction uses the dual int loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L208-L245
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrcFockZeroRight.lean#L208-L245

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

theorem Formalism.CohomologicalDescent.LR.dual_int_loc (hC : CoeffWord) (hL : LowerTriIntegral) (l : ℕ) (hl : l.Prime) (r : ℕ) (ν : Fin r → ℕ)
    (g : MvPolynomial (Fin r × Fin r) ℚ) (hg : g ∈ dualWeyl ℚ r r ν)
    (h : ∀ ω : List (Fin r × Fin r × ℕ), eval (idFrame ℚ r r) (applyWord ℚ ω g) ∈ Zl l) :
    ∃ m : ℤ, ¬ (l : ℤ) ∣ m ∧ ∃ g' ∈ dualWeyl ℤ r r ν, (m : ℚ) • g = intQ r r g' := by sorry
