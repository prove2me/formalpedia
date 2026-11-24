-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_cast_iff
-- name    : Formalism.CohomologicalDescent.LD.exp_le_cast_iff
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:06:06.844793+00:00
-- url     : https://prove2.me/theorems/6d64f5f2-c1c0-4480-937d-a50379741fd1
-- title:
--   LD: exp le cast iff
-- statement:
--   The LD construction uses the exp le cast iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L192-L195
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L192-L195

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

theorem Formalism.CohomologicalDescent.LD.exp_le_cast_iff (l : ℕ) {r r' : ℕ} (h : r' = r) (ν μ : Fin r → ℕ) (e : ℕ) :
    ExpLe l r' (fun a => ν (Fin.cast h a)) (fun a => μ (Fin.cast h a)) e ↔ ExpLe l r ν μ e := by sorry
