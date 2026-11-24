-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_glAct_full_split
-- name    : Formalism.GM.FrozenVariableComponents.glAct_full_split
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:19.995234+00:00
-- url     : https://prove2.me/theorems/8384dbd3-e299-4670-8ea5-baeb8881e354
-- title:
--   Frozen Variable Components: gl Act full split
-- statement:
--   The Frozen Variable Components construction uses the gl Act full split property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L505-L514
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L505-L514

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

theorem Formalism.GM.FrozenVariableComponents.glAct_full_split (LL : Letters N) (j : ℕ) (c d : Fin r) :
    glAct p LL N c d = glAct p LL j c d + restAct p LL j c d := by sorry
