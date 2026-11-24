-- Prove2me | Theorems.Thm_Formalism_G0_TailSumsP_cnt_succ_some
-- name    : Formalism.G0.TailSumsP.cnt_succ_some
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:10:31.473998+00:00
-- url     : https://prove2.me/theorems/9f82ef59-1fbe-4e02-a48a-3efd1821006a
-- title:
--   Tail Sums P: cnt succ some
-- statement:
--   The Tail Sums P construction uses the cnt succ some property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L69-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SubspaceCounting/SubspaceCountingProofs/TailSums.lean#L69-L74

import Definitions.Def_Formalism_SubspaceCounting_StatementC
import Definitions.Def_Formalism_SubspaceCounting_SubspaceCountingProofs_TailSums
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.G0
open Formalism.G0.TailSumsP

theorem Formalism.G0.TailSumsP.cnt_succ_some (steps : List (Option ℕ)) (i j : ℕ) (hij : i ≤ j) (hj : j < steps.length)
    {B : ℕ} (h : steps[j] = some B) : cnt steps i (j + 1) = cnt steps i j + 1 := by sorry
