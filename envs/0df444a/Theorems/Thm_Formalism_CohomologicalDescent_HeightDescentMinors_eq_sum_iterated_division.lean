-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_eq_sum_iterated_division
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_iterated_division
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:01.318781+00:00
-- url     : https://prove2.me/theorems/6cb6842a-4f2b-490b-a94b-05c32731a0a2
-- title:
--   Height Descent Minors: eq sum iterated division
-- statement:
--   The Height Descent Minors construction uses the eq sum iterated division property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L792-L801
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L792-L801

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.eq_sum_iterated_division (n : ℕ) (w : (R⟦X⟧)ˣ) (f : R⟦X⟧) (K : ℕ) :
    f = ∑ k ∈ range K, ((w : R⟦X⟧) * X ^ n) ^ k *
          (∑ j : Fin n, C (coeff (j : ℕ) ((divQuotient n w)^[k] f)) * X ^ (j : ℕ)) +
        ((w : R⟦X⟧) * X ^ n) ^ K * (divQuotient n w)^[K] f := by sorry
