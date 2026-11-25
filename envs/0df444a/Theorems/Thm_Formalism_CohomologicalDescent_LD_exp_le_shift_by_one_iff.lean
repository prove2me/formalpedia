-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_shift_by_one_iff
-- name    : Formalism.CohomologicalDescent.LD.exp_le_shift_by_one_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:33.402906+00:00
-- url     : https://prove2.me/theorems/16ad71d2-4975-478e-a474-84e3978d6908
-- title:
--   LD: exp le shift by one iff
-- statement:
--   The LD construction uses the exp le shift by one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L151-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L151-L182

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

theorem Formalism.CohomologicalDescent.LD.exp_le_shift_by_one_iff (l r : ℕ) (ν μ : Fin r → ℕ) (e : ℕ) (hν : Antitone ν) :
    ExpLe l r (fun a => ν a + 1) (fun a => μ a + 1) e ↔ ExpLe l r ν μ e := by sorry
