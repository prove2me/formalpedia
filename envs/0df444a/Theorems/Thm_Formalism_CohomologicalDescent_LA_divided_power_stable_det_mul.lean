-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LA_divided_power_stable_det_mul
-- name    : Formalism.CohomologicalDescent.LA.divided_power_stable_det_mul
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:58:41.025284+00:00
-- url     : https://prove2.me/theorems/ad0f4e82-f6e6-45f6-9da8-6ed6266b2022
-- title:
--   LA: divided power stable det mul
-- statement:
--   The LA construction uses the divided power stable det mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L77-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HighestWeightShiftEqDetMul.lean#L77-L95

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

theorem Formalism.CohomologicalDescent.LA.divided_power_stable_det_mul (R : Type) [CommRing R] {r : ℕ}
    (L : Submodule R (MvPolynomial (Fin r × Fin r) R))
    (hs : ∀ (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R), f ∈ L →
      rowDiv R a b k f ∈ L) (a b : Fin r) (k : ℕ) (f : MvPolynomial (Fin r × Fin r) R)
    (hf : f ∈ L.map (LinearMap.mulLeft R (genericDet R r))) :
    rowDiv R a b k f ∈ L.map (LinearMap.mulLeft R (genericDet R r)) := by sorry
