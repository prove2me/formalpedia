-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_sums_tele
-- name    : Formalism.CohomologicalDescent.sums_tele
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:35:06.114681+00:00
-- url     : https://prove2.me/theorems/679951d3-512b-4d0a-a85c-da3d9f955769
-- title:
--   Cohomological Descent: sums tele
-- statement:
--   The Cohomological Descent construction uses the sums tele property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L171-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SharperSizeNeedsMleKFalse.lean#L171-L179

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

theorem Formalism.CohomologicalDescent.sums_tele (F : ℝ → ℝ) (n : ℕ) :
    ∑ d ∈ Finset.Icc 1 n, (F (d : ℝ) - F ((d : ℝ) - 1)) = F n - F 0 := by sorry
