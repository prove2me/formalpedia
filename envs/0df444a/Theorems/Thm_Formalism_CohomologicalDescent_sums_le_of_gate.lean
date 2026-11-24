-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_sums_le_of_gate
-- name    : Formalism.CohomologicalDescent.sums_le_of_gate
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:35:25.919537+00:00
-- url     : https://prove2.me/theorems/2cac5b04-8891-44a4-a26d-2107ac976755
-- title:
--   Cohomological Descent: sums le of gate
-- statement:
--   The Cohomological Descent construction uses the sums le of gate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L26-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L26-L29

import Mathlib
import Definitions.Def_Formalism_PieriBlockIdeals_Statement
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SharperSizeNeedsMleKFalse
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.CohomologicalDescent
open Classical

theorem Formalism.CohomologicalDescent.sums_le_of_gate (l D : ℕ) (hD : 1 ≤ D) (hg : ((d0 l (D : ℤ) : ℕ) : ℤ) < (D : ℤ)) :
    (l : ℤ) ≤ (D : ℤ) - (d0 l (D : ℤ) : ℤ) := by sorry
