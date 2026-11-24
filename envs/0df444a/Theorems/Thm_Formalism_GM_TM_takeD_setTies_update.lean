-- Prove2me | Theorems.Thm_Formalism_GM_TM_takeD_setTies_update
-- name    : Formalism.GM.TM.takeD_setTies_update
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:47:32.868285+00:00
-- url     : https://prove2.me/theorems/409c03c1-1373-49d1-86c9-00ce1c35fa17
-- title:
--   TM: take D set Ties update
-- statement:
--   The TM construction uses the take D set Ties update property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L13-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L13-L26

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_TheoremM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.TM
open M MvPolynomial Finset
variable {N : ℕ}

theorem Formalism.GM.TM.takeD_setTies_update (LL : Letters N) (T : TieData) (n : Fin T.t → ℕ) (i : Fin T.t) (x : ℕ) :
    (LL.setTies T (Function.update n i x)).takeD (T.pos i + 1) = (LL.setTies T n).takeD (T.pos i + 1) := by sorry
