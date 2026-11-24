-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_hasSubst_gammaSeries
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.hasSubst_gammaSeries
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:52:54.99732+00:00
-- url     : https://prove2.me/theorems/b4068211-b84a-4a36-b658-153bd95ab016
-- title:
--   Frobenius Period Change: has Subst gamma Series
-- statement:
--   The Frobenius Period Change construction uses the has Subst gamma Series property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L41-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L41-L45

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
variable {R : Type} [CommRing R]

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.hasSubst_gammaSeries (lam : R) (un : R⟦X⟧) : HasSubst (gamSer lam un) := by sorry
