-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_HeightDescentMinors_exists_largest_moved_point
-- name    : Formalism.CohomologicalDescent.HeightDescentMinors.exists_largest_moved_point
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:31:04.347484+00:00
-- url     : https://prove2.me/theorems/38dd97d8-6024-4973-ac8b-e3fbad2e4575
-- title:
--   Height Descent Minors: exists largest moved point
-- statement:
--   The Height Descent Minors construction uses the exists largest moved point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1875-L1897
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/HeightDescentMinors.lean#L1875-L1897

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

theorem Formalism.CohomologicalDescent.HeightDescentMinors.exists_largest_moved_point {N : ℕ} (σ : Equiv.Perm (Fin N)) (hσ : σ ≠ 1) :
    ∃ j0, σ j0 < j0 ∧ ∀ j, j0 < j → σ j = j := by sorry
