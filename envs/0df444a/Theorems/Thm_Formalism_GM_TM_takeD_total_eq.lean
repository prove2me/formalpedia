-- Prove2me | Theorems.Thm_Formalism_GM_TM_takeD_total_eq
-- name    : Formalism.GM.TM.takeD_total_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:07.305108+00:00
-- url     : https://prove2.me/theorems/a5082857-3a9e-4030-8a32-0d4fa9a3982e
-- title:
--   TM: take D total eq
-- statement:
--   The TM construction uses the take D total eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L45-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L45-L69

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

theorem Formalism.GM.TM.takeD_total_eq (LL : Letters N) (T : TieData) (i : Fin T.t) (h : T.pos i + 1 < N) :
    (LL.takeD (T.pos i + 1)).total = T.S LL i := by sorry
