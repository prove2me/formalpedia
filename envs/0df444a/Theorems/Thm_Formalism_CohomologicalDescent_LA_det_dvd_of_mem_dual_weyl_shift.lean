-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_det_dvd_of_mem_dual_weyl_shift
-- name    : Formalism.CohomologicalDescent.LA.det_dvd_of_mem_dual_weyl_shift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:48.02247+00:00
-- url     : https://prove2.me/theorems/ce1f9086-93fa-442e-b042-f4ae811a9db9
-- title:
--   LA: det dvd of mem dual weyl shift
-- statement:
--   The LA construction uses the det dvd of mem dual weyl shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L399-L407
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L399-L407

import Definitions.Def_Formalism_PieriBlockIdeals_ExZTranslate
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HighestWeightShiftEqDetMul
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LA
open Formalism.GradedWeylDivisibility

theorem Formalism.CohomologicalDescent.LA.det_dvd_of_mem_dual_weyl_shift {r : ℕ} (ν : Fin r → ℕ) (hν : Antitone ν)
    {f : MvPolynomial (Fin r × Fin r) ℤ} (hf : f ∈ dualWeyl ℤ r r (fun a => ν a + 1)) :
    genericDet ℤ r ∣ f := by sorry
