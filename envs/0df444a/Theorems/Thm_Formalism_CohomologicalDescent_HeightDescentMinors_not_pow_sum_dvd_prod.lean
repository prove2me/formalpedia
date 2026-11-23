-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_not_pow_sum_dvd_prod
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.not_pow_sum_dvd_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:32:09.198828+00:00
-- url     : https://prove2.me/theorems/844fc46f-5c00-4716-b79d-1748aacd66e7
-- title:
--   Height Descent Minors: not pow sum dvd prod
-- statement:
--   The Height Descent Minors construction uses the not pow sum dvd prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1511-L1522
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1511-L1522

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.not_pow_sum_dvd_prod [IsDomain R] {π : R} (hπ : Prime π) {κ : Type} (s : Finset κ)
    (v : κ → ℕ) (y : κ → R) (h : ∀ r ∈ s, ¬ π ^ (v r + 1) ∣ y r) :
    ¬ π ^ (∑ r ∈ s, v r + 1) ∣ ∏ r ∈ s, y r := by sorry
