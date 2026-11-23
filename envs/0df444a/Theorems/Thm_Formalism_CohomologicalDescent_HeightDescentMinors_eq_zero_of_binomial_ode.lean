-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_zero_of_binomial_ode
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.eq_zero_of_binomial_ode
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:58.76675+00:00
-- url     : https://prove2.me/theorems/2bb5ddc0-1d68-4c4a-9028-e1ac2a164aba
-- title:
--   Height Descent Minors: eq zero of binomial ode
-- statement:
--   The Height Descent Minors construction uses the eq zero of binomial ode property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L23-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L23-L37

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
variable {R : Type*} [CommRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.eq_zero_of_binomial_ode [IsAddTorsionFree R] (c : R) (H : R⟦X⟧)
    (h : (1 + X) * d⁄dX R H = C c * H) (h0 : constantCoeff H = 0) : H = 0 := by sorry
