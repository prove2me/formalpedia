-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_prod_sub_prod
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.dvd_prod_sub_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:54.385522+00:00
-- url     : https://prove2.me/theorems/7de5866a-837c-4bd6-abf3-505305516601
-- title:
--   Height Descent Minors: dvd prod sub prod
-- statement:
--   The Height Descent Minors construction uses the dvd prod sub prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1128-L1140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1128-L1140

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.dvd_prod_sub_prod {R ι : Type} [CommRing R] (s : Finset ι) (a b : ι → R) (x : R)
    (h : ∀ i ∈ s, x ∣ a i - b i) : x ∣ ∏ i ∈ s, a i - ∏ i ∈ s, b i := by sorry
