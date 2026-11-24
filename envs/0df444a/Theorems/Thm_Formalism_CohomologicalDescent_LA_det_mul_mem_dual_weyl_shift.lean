-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mul_mem_dual_weyl_shift
-- name    : Formalism.CohomologicalDescent.LA.det_mul_mem_dual_weyl_shift
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:59:44.029281+00:00
-- url     : https://prove2.me/theorems/8aaf028d-f5ff-4a6e-bdb8-04160ec8b766
-- title:
--   LA: det mul mem dual weyl shift
-- statement:
--   The LA construction uses the det mul mem dual weyl shift property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L309-L326
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L309-L326

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

theorem Formalism.CohomologicalDescent.LA.det_mul_mem_dual_weyl_shift {r : ℕ} (ν : Fin r → ℕ) {g : MvPolynomial (Fin r × Fin r) ℤ}
    (hg : g ∈ dualWeyl ℤ r r ν) : genericDet ℤ r * g ∈ dualWeyl ℤ r r (fun a => ν a + 1) := by sorry
