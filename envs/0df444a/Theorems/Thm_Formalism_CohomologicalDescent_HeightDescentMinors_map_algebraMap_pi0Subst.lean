-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_map_algebraMap_pi0Subst
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.map_algebraMap_pi0Subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:04.796147+00:00
-- url     : https://prove2.me/theorems/8f2af96f-54f9-4a94-8032-4a4eb2c614cb
-- title:
--   Height Descent Minors: map algebra Map pi0 Subst
-- statement:
--   The Height Descent Minors construction uses the map algebra Map pi0 Subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1209-L1212
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1209-L1212

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.map_algebraMap_pi0Subst (hm : MuFacts) (f : ℤ_[l]⟦X⟧) :
    PowerSeries.map (algebraMap ℤ_[l] O) (inc l ℤ_[l] f) =
      inc l O (PowerSeries.map (algebraMap ℤ_[l] O) f) := by sorry
