-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_algebraMap_unit_ne_zero
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.reduction_algebraMap_unit_ne_zero
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:57.175139+00:00
-- url     : https://prove2.me/theorems/2422ffa4-aa6c-4507-bf2e-460a278ca745
-- title:
--   Frobenius Period Change: reduction algebra Map unit ne zero
-- statement:
--   The Frobenius Period Change construction uses the reduction algebra Map unit ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L701-L703
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L701-L703

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
variable {ι : Type} {t n : ℕ} {O F : Type} [CommRing O] [Field F]

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.reduction_algebraMap_unit_ne_zero (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] (red : O →+* F) (c : ℤ_[l])
    (hc : IsUnit c) : red (algebraMap ℤ_[l] O c) ≠ 0 := by sorry
