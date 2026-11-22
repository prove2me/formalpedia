-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_snoc_vec_castSucc
-- name    : Formalism.GM.FrozenVariableComponents.snoc_vec_castSucc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:32:48.665504+00:00
-- url     : https://prove2.me/theorems/e34fd79b-2559-4e76-84fd-4763db37c0c4
-- title:
--   Frozen Variable Components: snoc vec cast Succ
-- statement:
--   The Frozen Variable Components construction uses the snoc vec cast Succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L257-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L257-L259

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

theorem Formalism.GM.FrozenVariableComponents.snoc_vec_castSucc (LL : Letters N) (n : ℕ) (i : Fin N) :
    (LL.snoc n).vec (Fin.castSucc i) = LL.vec i := by sorry
