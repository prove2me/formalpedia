-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_of_binomial_ode_of_constantCoeff_eq
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.eq_of_binomial_ode_of_constantCoeff_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:03.019806+00:00
-- url     : https://prove2.me/theorems/c14069bf-78bb-4598-ab72-2df00ccb08bd
-- title:
--   Height Descent Minors: eq of binomial ode of constant Coeff eq
-- statement:
--   The Height Descent Minors construction uses the eq of binomial ode of constant Coeff eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L39-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L39-L44

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.eq_of_binomial_ode_of_constantCoeff_eq [IsAddTorsionFree R] (c : R) (F G : R⟦X⟧)
    (hF : (1 + X) * d⁄dX R F = C c * F) (hG : (1 + X) * d⁄dX R G = C c * G)
    (h0 : constantCoeff F = constantCoeff G) : F = G := by sorry
