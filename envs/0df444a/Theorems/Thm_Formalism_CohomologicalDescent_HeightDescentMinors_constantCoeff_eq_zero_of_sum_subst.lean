-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_constantCoeff_eq_zero_of_sum_subst
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_eq_zero_of_sum_subst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:30:56.76557+00:00
-- url     : https://prove2.me/theorems/ce169ae4-9cd7-4a68-9a30-ff8a6d3e4114
-- title:
--   Height Descent Minors: constant Coeff eq zero of sum subst
-- statement:
--   The Height Descent Minors construction uses the constant Coeff eq zero of sum subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L835-L859
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L835-L859

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.constantCoeff_eq_zero_of_sum_subst (n : ℕ) (hn : 0 < n) (w : (R⟦X⟧)ˣ) (d : Fin n → R⟦X⟧)
    (h0 : ∑ j : Fin n, (d j).subst ((w : R⟦X⟧) * X ^ n) * X ^ (j : ℕ) = 0) (i : Fin n) :
    constantCoeff (d i) = 0 := by sorry
