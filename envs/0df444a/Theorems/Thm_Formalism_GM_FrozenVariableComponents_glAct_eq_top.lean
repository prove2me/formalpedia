-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_eq_top
-- name    : Formalism.GM.FrozenVariableComponents.glAct_eq_top
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:21:20.292817+00:00
-- url     : https://prove2.me/theorems/0d93bb34-0264-44d6-ab87-a348e6e063aa
-- title:
--   Frozen Variable Components: gl Act eq top
-- statement:
--   The Frozen Variable Components construction uses the gl Act eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L498-L499
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L498-L499

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable (p : ℕ) [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.FrozenVariableComponents.glAct_eq_top (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL j c d = ∑ i : Fin N, if (i : ℕ) < j then top p LL i c d else 0 := by sorry
