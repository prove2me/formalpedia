-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_map_X_sub_C_prime_pow_eq_X_pow
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_X_sub_C_prime_pow_eq_X_pow
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:53:31.637583+00:00
-- url     : https://prove2.me/theorems/ad28309a-c0df-43cf-8cce-4e11a2cf78f6
-- title:
--   Frobenius Period Change: map X sub C prime pow eq X pow
-- statement:
--   The Frobenius Period Change construction uses the map X sub C prime pow eq X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L631-L633
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L631-L633

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.map_X_sub_C_prime_pow_eq_X_pow (l : ℕ) [CharP F l] (red : O →+* F) (m : ℕ) :
    PowerSeries.map red ((X - C (l : O)) ^ m) = X ^ m := by sorry
