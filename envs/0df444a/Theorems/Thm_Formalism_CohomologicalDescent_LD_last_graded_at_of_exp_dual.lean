-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_last_graded_at_of_exp_dual
-- name    : Formalism.CohomologicalDescent.LD.last_graded_at_of_exp_dual
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:05:32.202353+00:00
-- url     : https://prove2.me/theorems/fa054957-dde3-45dc-8bd8-f4898f479ad4
-- title:
--   LD: last graded at of exp dual
-- statement:
--   The LD construction uses the last graded at of exp dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L235-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L235-L266

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

theorem Formalism.CohomologicalDescent.LD.last_graded_at_of_exp_dual (hE : ExpDual) (hD : LemmaDGraded) (l p q w M : ℕ) (lam2 : Fin q → ℕ) (ξ : Fin (q + p) → ℤ)
    (hl : l.Prime) (ha : Antitone lam2) (hb : ∀ b, w ≤ lam2 b ∧ lam2 b ≤ M) (hwM : w ≤ M) (hξ : Antitone ξ) :
    LemmaDLastGradedAt l p q w M lam2 ξ := by sorry
