-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_rest_comm
-- name    : Formalism.GM.FrozenVariableComponents.rest_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:19.881412+00:00
-- url     : https://prove2.me/theorems/b2331bcd-33bd-4b47-9cd7-f3fa3509be14
-- title:
--   Frozen Variable Components: rest comm
-- statement:
--   The Frozen Variable Components construction uses the rest comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L525-L533
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L525-L533

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

theorem Formalism.GM.FrozenVariableComponents.rest_comm (LL : Letters N) (j : ℕ) (c d c' d' : Fin r) (F : MvPolynomial (Fin N × Fin r) ℚ_[p]) :
    restAct p LL j c d (glAct p LL j c' d' F) = glAct p LL j c' d' (restAct p LL j c d F) := by sorry
