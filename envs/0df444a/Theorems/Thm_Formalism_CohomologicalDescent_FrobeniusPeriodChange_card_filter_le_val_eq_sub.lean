-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_card_filter_le_val_eq_sub
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.card_filter_le_val_eq_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:53:08.437214+00:00
-- url     : https://prove2.me/theorems/763761b6-d5ae-41d6-81aa-4489fd5a5704
-- title:
--   Frobenius Period Change: card filter le val eq sub
-- statement:
--   The Frobenius Period Change construction uses the card filter le val eq sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L993-L1005
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L993-L1005

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.card_filter_le_val_eq_sub (N m : ℕ) (hm : m ≤ N) :
    (Finset.univ.filter fun a : Fin N => m ≤ (a : ℕ)).card = N - m := by sorry
