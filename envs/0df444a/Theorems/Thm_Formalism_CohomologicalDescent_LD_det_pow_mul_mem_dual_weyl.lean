-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LD_det_pow_mul_mem_dual_weyl
-- name    : Formalism.CohomologicalDescent.LD.det_pow_mul_mem_dual_weyl
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T23:07:08.795232+00:00
-- url     : https://prove2.me/theorems/a10f9727-6775-48d3-8076-a9394515eeeb
-- title:
--   LD: det pow mul mem dual weyl
-- statement:
--   The LD construction uses the det pow mul mem dual weyl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L436-L442
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightProdLeadingMinors.lean#L436-L442

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

theorem Formalism.CohomologicalDescent.LD.det_pow_mul_mem_dual_weyl {r : ℕ} (ν : Fin r → ℕ) (c : ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (hg : g ∈ dualWeyl ℤ r r ν) : genericDet ℤ r ^ c * g ∈ dualWeyl ℤ r r (fun a => ν a + c) := by sorry
