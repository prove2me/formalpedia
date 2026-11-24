-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_sum_tail_le_sum_of_antitone
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.sum_tail_le_sum_of_antitone
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:52.996057+00:00
-- url     : https://prove2.me/theorems/e46f2979-49a3-45b0-b25c-e4698ec299ef
-- title:
--   Frobenius Period Change: sum tail le sum of antitone
-- statement:
--   The Frobenius Period Change construction uses the sum tail le sum of antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L955-L991
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L955-L991

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.sum_tail_le_sum_of_antitone {N : ℕ} (f : Fin N → ℤ) (hf : Antitone f) (m : ℕ) (J : Finset (Fin N))
    (hJ : J.card = (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card) :
    ∑ a ∈ Finset.univ.filter (fun a : Fin N => m ≤ (a : ℕ)), f a ≤ ∑ a ∈ J, f a := by sorry
