-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_coeff_eq_zero_of_subst_sum_eq_zero
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.coeff_eq_zero_of_subst_sum_eq_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:39.583587+00:00
-- url     : https://prove2.me/theorems/1939f533-6077-47c4-aea1-4a07102cd9b3
-- title:
--   Height Descent Minors: coeff eq zero of subst sum eq zero
-- statement:
--   The Height Descent Minors construction uses the coeff eq zero of subst sum eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L861-L883
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L861-L883

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.coeff_eq_zero_of_subst_sum_eq_zero (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (k : ℕ) :
    ∀ d : Fin n → R⟦X⟧, ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0 →
      ∀ j, coeff k (d j) = 0 := by sorry
