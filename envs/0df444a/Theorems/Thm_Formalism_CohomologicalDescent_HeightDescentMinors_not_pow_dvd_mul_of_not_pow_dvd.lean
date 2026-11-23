-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_not_pow_dvd_mul_of_not_pow_dvd
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.not_pow_dvd_mul_of_not_pow_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:15.480543+00:00
-- url     : https://prove2.me/theorems/59d83d49-05b0-4224-ac86-5b5cbb6a7d89
-- title:
--   Height Descent Minors: not pow dvd mul of not pow dvd
-- statement:
--   The Height Descent Minors construction uses the not pow dvd mul of not pow dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1500-L1509
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1500-L1509

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.not_pow_dvd_mul_of_not_pow_dvd [IsDomain R] {π x y : R} {a b : ℕ} (hπ : Prime π)
    (hx : ¬ π ^ (a + 1) ∣ x) (hy : ¬ π ^ (b + 1) ∣ y) : ¬ π ^ (a + b + 1) ∣ x * y := by sorry
