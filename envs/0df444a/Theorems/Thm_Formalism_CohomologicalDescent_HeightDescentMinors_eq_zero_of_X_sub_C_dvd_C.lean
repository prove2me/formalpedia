-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_zero_of_X_sub_C_dvd_C
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.eq_zero_of_X_sub_C_dvd_C
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:40.329801+00:00
-- url     : https://prove2.me/theorems/82deb10e-fc98-4b63-b49b-8a78f32531e8
-- title:
--   Height Descent Minors: eq zero of X sub C dvd C
-- statement:
--   The Height Descent Minors construction uses the eq zero of X sub C dvd C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1710-L1714
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1710-L1714

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.eq_zero_of_X_sub_C_dvd_C {O : Type} [CommRing O] [IsDomain O] (I : Ideal O) [IsAdicComplete I O] (c : O)
    (hc : c ∈ I) (b : O) (h : (X - C c : O⟦X⟧) ∣ C b) : b = 0 := by sorry
