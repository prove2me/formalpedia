-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_mem_dual_weyl_of_det_mul
-- name    : Formalism.CohomologicalDescent.LA.mem_dual_weyl_of_det_mul
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:58:43.758023+00:00
-- url     : https://prove2.me/theorems/9e544b8d-d90b-49ca-b55e-32a1e7011882
-- title:
--   LA: mem dual weyl of det mul
-- statement:
--   The LA construction uses the mem dual weyl of det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L328-L353
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L328-L353

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

theorem Formalism.CohomologicalDescent.LA.mem_dual_weyl_of_det_mul {r : ℕ} (ν : Fin r → ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (h : genericDet ℤ r * g ∈ dualWeyl ℤ r r (fun a => ν a + 1)) : g ∈ dualWeyl ℤ r r ν := by sorry
