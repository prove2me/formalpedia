-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_dvd_subst_of_constantCoeff_zero
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.dvd_subst_of_constantCoeff_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:10.600269+00:00
-- url     : https://prove2.me/theorems/41cb28a1-f1c8-41f6-8bd2-14a714e49180
-- title:
--   Height Descent Minors: dvd subst of constant Coeff zero
-- statement:
--   The Height Descent Minors construction uses the dvd subst of constant Coeff zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1120-L1121
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1120-L1121

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.dvd_subst_of_constantCoeff_zero {R : Type} [CommRing R] (a f : R⟦X⟧) (ha : HasSubst a)
    (hf : constantCoeff f = 0) : a ∣ f.subst a := by sorry
