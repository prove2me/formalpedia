-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_FrobeniusPeriodChange_pi0Subst_reduction_holds
-- name    : Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_reduction_holds
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:53:24.875278+00:00
-- url     : https://prove2.me/theorems/4c3dfbf2-21de-4b21-a0b0-f8f85c54ff0d
-- title:
--   Frobenius Period Change: pi0 Subst reduction holds
-- statement:
--   The Frobenius Period Change construction uses the pi0 Subst reduction holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L98-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeckeLFunctionIdealEulerProduct.lean#L98-L110

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

theorem Formalism.CohomologicalDescent.FrobeniusPeriodChange.pi0Subst_reduction_holds : IncRed := by sorry
