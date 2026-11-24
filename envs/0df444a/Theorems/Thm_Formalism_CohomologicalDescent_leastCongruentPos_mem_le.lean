-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_leastCongruentPos_mem_le
-- name    : Formalism.CohomologicalDescent.leastCongruentPos_mem_le
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:35:18.641806+00:00
-- url     : https://prove2.me/theorems/16785471-362a-401d-81eb-b417c6c95497
-- title:
--   Cohomological Descent: least Congruent Pos mem le
-- statement:
--   The Cohomological Descent construction uses the least Congruent Pos mem le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L19-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L19-L24

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

theorem Formalism.CohomologicalDescent.leastCongruentPos_mem_le (l D : ℕ) (hD : 1 ≤ D) :
    1 ≤ d0 l (D : ℤ) ∧ (l : ℤ) ∣ (D : ℤ) - (d0 l (D : ℤ) : ℤ) ∧ d0 l (D : ℤ) ≤ D := by sorry
