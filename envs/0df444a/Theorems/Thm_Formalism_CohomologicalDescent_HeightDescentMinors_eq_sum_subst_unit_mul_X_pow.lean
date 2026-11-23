-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_subst_unit_mul_X_pow
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_subst_unit_mul_X_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:28:40.244539+00:00
-- url     : https://prove2.me/theorems/4d67bc38-153b-46c1-9f47-15967fd8982b
-- title:
--   Height Descent Minors: eq sum subst unit mul X pow
-- statement:
--   The Height Descent Minors construction uses the eq sum subst unit mul X pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L803-L833
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L803-L833

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
variable {R : Type} [CommRing R]

theorem Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_subst_unit_mul_X_pow (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) :
    f = ∑ j : Fin n, (PowerSeries.mk fun k => coeff (j : ℕ) ((divQuotient n w)^[k] f)).subst
          ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) := by sorry
