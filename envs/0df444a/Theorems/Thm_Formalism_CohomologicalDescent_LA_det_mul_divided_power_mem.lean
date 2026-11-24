-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_det_mul_divided_power_mem
-- name    : Formalism.CohomologicalDescent.LA.det_mul_divided_power_mem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:34.896614+00:00
-- url     : https://prove2.me/theorems/87710078-4bd6-4349-9876-3fa504194f31
-- title:
--   LA: det mul divided power mem
-- statement:
--   The LA construction uses the det mul divided power mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L97-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L97-L114

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

theorem Formalism.CohomologicalDescent.LA.det_mul_divided_power_mem (R : Type) [CommRing R] {r : ℕ}
    (W : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hW : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ W →
      rowDiv R a b k f ∈ W) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : genericDet R r * f ∈ W) : genericDet R r * rowDiv R a b k f ∈ W := by sorry
