-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_subst_eq_sum_range_add_pow_mul
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.subst_eq_sum_range_add_pow_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:04:09.472429+00:00
-- url     : https://prove2.me/theorems/70245275-535a-4209-b9f7-9a4065d94ffa
-- title:
--   Height Descent Minors: subst eq sum range add pow mul
-- statement:
--   The Height Descent Minors construction uses the subst eq sum range add pow mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L724-L742
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L724-L742

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.subst_eq_sum_range_add_pow_mul {a : R⟦X⟧} (ha : HasSubst a) (K : ℕ) (g : R⟦X⟧) :
    ∃ h : R⟦X⟧, g.subst a = ∑ k ∈ range K, C (coeff k g) * a ^ k + a ^ K * h := by sorry
