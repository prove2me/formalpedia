-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_det_map
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_det_map
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:21.121945+00:00
-- url     : https://prove2.me/theorems/f7cb64e4-1ce0-4e6e-8c08-360bab36ea78
-- title:
--   Frobenius Period Change: pi0 Subst det map
-- statement:
--   The Frobenius Period Change construction uses the pi0 Subst det map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L1083-L1088
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L1083-L1088

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_LemmaWFromLattice
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeckeLFunctionIdealEulerProduct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset PowerSeries
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.FrobeniusPeriodChange
open Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_det_map (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O] {L : Type}
    [CommRing L] (jj : O⟦X⟧ →+* L⟦X⟧) {t : ℕ} (M : Matrix (Fin t) (Fin t) O⟦X⟧) :
    jj (inc l O M.det) = (M.map (fun y => jj (inc l O y))).det := by sorry
