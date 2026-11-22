-- Prove2me | Theorems.Thm_Formalism_GM_TM_setTies_deg_eta
-- name    : Formalism.GM.TM.setTies_deg_eta
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:15:46.530158+00:00
-- url     : https://prove2.me/theorems/4ce6982c-b2ed-4eeb-aba3-9ec9f049c588
-- title:
--   TM: set Ties deg eta
-- statement:
--   The TM construction uses the set Ties deg eta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L28-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L28-L35

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

theorem Formalism.GM.TM.setTies_deg_eta (LL : Letters N) (T : TieData) (hT : StrictMono T.pos) (n : Fin T.t → ℕ) (i : Fin T.t)
    (h : T.pos i + 1 < N) : (LL.setTies T n).deg ⟨T.pos i + 1, h⟩ = n i := by sorry
