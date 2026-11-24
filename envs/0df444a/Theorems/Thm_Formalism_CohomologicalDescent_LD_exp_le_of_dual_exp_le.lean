-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_exp_le_of_dual_exp_le
-- name    : Formalism.CohomologicalDescent.LD.exp_le_of_dual_exp_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:05:19.571172+00:00
-- url     : https://prove2.me/theorems/b727f008-c317-4f15-8279-190c4dadcaf5
-- title:
--   LD: exp le of dual exp le
-- statement:
--   The LD construction uses the exp le of dual exp le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L1006-L1047
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L1006-L1047

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

theorem Formalism.CohomologicalDescent.LD.exp_le_of_dual_exp_le (hN : NablaDual) (hW : WeylDual) (hT : DualWeight) (hC : CofCof) (l r M : ℕ) (ν μ : Fin r → ℕ)
    (e : ℕ) (hl : l.Prime) (hν : Antitone ν) (hνM : ∀ a, ν a ≤ M) (hμM : ∀ a, μ a ≤ M)
    (h : ExpLe l r (dualWt M ν) (dualWt M μ) e) : ExpLe l r ν μ e := by sorry
