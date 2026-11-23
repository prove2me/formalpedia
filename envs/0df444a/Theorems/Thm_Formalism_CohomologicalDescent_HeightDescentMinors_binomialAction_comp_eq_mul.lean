-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_binomialAction_comp_eq_mul
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.binomialAction_comp_eq_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:36.281085+00:00
-- url     : https://prove2.me/theorems/a180afc4-dbda-4841-abad-f0f0a13c4a1e
-- title:
--   Height Descent Minors: binomial Action comp eq mul
-- statement:
--   The Height Descent Minors construction uses the binomial Action comp eq mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L154-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L154-L158

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
variable (l : ℕ) [Fact l.Prime] (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.binomialAction_comp_eq_mul (c d : ℤ_[l]) (f : O⟦X⟧) :
    act l O c (act l O d f) = act l O (d * c) f := by sorry
