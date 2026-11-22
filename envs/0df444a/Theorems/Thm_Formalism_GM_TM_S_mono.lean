-- Prove2me | Theorems.Thm_Formalism_GM_TM_S_mono
-- name    : Formalism.GM.TM.S_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:22:52.535466+00:00
-- url     : https://prove2.me/theorems/139641f7-8ed3-44d6-bcba-d1ff476b3021
-- title:
--   TM: S mono
-- statement:
--   The TM construction uses the S mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L71-L78
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L71-L78

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

theorem Formalism.GM.TM.S_mono (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n' i) (i : Fin T.t) :
    T.S (LL.setTies T n) i ≤ T.S (LL.setTies T n') i := by sorry
