-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_prod_sub_prod_of_dvd_sub
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.dvd_prod_sub_prod_of_dvd_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:03.52526+00:00
-- url     : https://prove2.me/theorems/2e2e911d-3e34-4a30-b59a-23b514ed3eeb
-- title:
--   Height Descent Minors: dvd prod sub prod of dvd sub
-- statement:
--   The Height Descent Minors construction uses the dvd prod sub prod of dvd sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L438-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L438-L450

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.dvd_prod_sub_prod_of_dvd_sub {R ι : Type} [CommRing R] (x : R) (s : Finset ι) (F G : ι → R)
    (h : ∀ i ∈ s, x ∣ F i - G i) : x ∣ ∏ i ∈ s, F i - ∏ i ∈ s, G i := by sorry
