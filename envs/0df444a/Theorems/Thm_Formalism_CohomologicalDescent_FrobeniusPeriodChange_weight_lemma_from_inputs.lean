-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_weight_lemma_from_inputs
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_lemma_from_inputs
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:21:36.784899+00:00
-- url     : https://prove2.me/theorems/569a3a13-c520-45a9-b479-6a97d09507a3
-- title:
--   Frobenius Period Change: weight lemma from inputs
-- statement:
--   The Frobenius Period Change construction uses the weight lemma from inputs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L830-L863
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L830-L863

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.weight_lemma_from_inputs : LemmaWFromInputs := by sorry
