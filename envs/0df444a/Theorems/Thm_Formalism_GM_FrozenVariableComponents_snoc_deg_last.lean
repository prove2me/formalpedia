-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_deg_last
-- name    : Formalism.GM.FrozenVariableComponents.snoc_deg_last
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:44.319634+00:00
-- url     : https://prove2.me/theorems/d11301b1-c8cc-4be6-a09a-a7e22618c869
-- title:
--   Frozen Variable Components: snoc deg last
-- statement:
--   The Frozen Variable Components construction uses the snoc deg last property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L268-L269
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L268-L269

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

theorem Formalism.GM.FrozenVariableComponents.snoc_deg_last (LL : Letters N) (n : ℕ) : (LL.snoc n).deg (Fin.last N) = n := by sorry
