-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_act_finset_prod
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.act_finset_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:29.047747+00:00
-- url     : https://prove2.me/theorems/eff88f1c-4d1d-4394-b29e-acd5ac3dbb66
-- title:
--   Height Descent Minors: act finset prod
-- statement:
--   The Height Descent Minors construction uses the act finset prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L355-L358
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L355-L358

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
variable (l : ℕ) [Fact l.Prime]
variable (O : Type) [CommRing O] [Algebra ℤ_[l] O]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.act_finset_prod {ι : Type*} (c : ℤ_[l]) (s : Finset ι) (f : ι → O⟦X⟧) :
    act l O c (∏ i ∈ s, f i) = ∏ i ∈ s, act l O c (f i) := by sorry
