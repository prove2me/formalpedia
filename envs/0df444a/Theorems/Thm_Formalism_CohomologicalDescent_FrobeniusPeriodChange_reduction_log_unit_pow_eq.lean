-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_reduction_log_unit_pow_eq
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.reduction_log_unit_pow_eq
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:29.61105+00:00
-- url     : https://prove2.me/theorems/bd98c4f2-b77f-4406-8bf5-a2a61da86f87
-- title:
--   Frobenius Period Change: reduction log unit pow eq
-- statement:
--   The Frobenius Period Change construction uses the reduction log unit pow eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L635-L679
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L635-L679

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.reduction_log_unit_pow_eq (l : ℕ) [Fact l.Prime] [Algebra ℤ_[l] O] [CharP F l] (red : O →+* F)
    (u : ℤ_[l]ˣ) (c r : ℤ_[l]) (m : ℤ) (hu : (u : ℤ_[l]) = 1 + (l : ℤ_[l]) * c)
    (hr : ((u ^ (-m) : ℤ_[l]ˣ) : ℤ_[l]) = 1 + (l : ℤ_[l]) * r) :
    red (algebraMap ℤ_[l] O r) = -red (algebraMap ℤ_[l] O c) * ((m : ℤ) : F) := by sorry
