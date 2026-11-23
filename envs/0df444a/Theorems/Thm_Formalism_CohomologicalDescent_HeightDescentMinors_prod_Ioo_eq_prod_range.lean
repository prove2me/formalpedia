-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_prod_Ioo_eq_prod_range
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.prod_Ioo_eq_prod_range
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:20.730944+00:00
-- url     : https://prove2.me/theorems/6ce22e52-4732-4276-a343-f71b2b078a07
-- title:
--   Height Descent Minors: prod Ioo eq prod range
-- statement:
--   The Height Descent Minors construction uses the prod Ioo eq prod range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L452-L457
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L452-L457

import Definitions.Def_Formalism_PieriBlockIdeals_CapelliCentralEnveloping
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_HeightDescentMinors
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
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.HeightDescentMinors

theorem Formalism.CohomologicalDescent.HeightDescentMinors.prod_Ioo_eq_prod_range {M : Type} [CommMonoid M] (l : ℕ) (F : ℕ → M) :
    ∏ c ∈ Finset.Ioo 0 l, F c = ∏ k ∈ Finset.range (l - 1), F (k + 1) := by sorry
