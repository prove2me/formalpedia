-- Prove2me | Theorems.Thm_Formalism_GM_TM_setTies_deg_mono
-- name    : Formalism.GM.TM.setTies_deg_mono
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:23:11.825799+00:00
-- url     : https://prove2.me/theorems/ce96f49a-769e-456e-a9bf-933a3abc33cd
-- title:
--   TM: set Ties deg mono
-- statement:
--   The TM construction uses the set Ties deg mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L37-L43

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

theorem Formalism.GM.TM.setTies_deg_mono (LL : Letters N) (T : TieData) (n n' : Fin T.t → ℕ) (hn : ∀ i, n i ≤ n' i) (a : Fin N) :
    (LL.setTies T n).deg a ≤ (LL.setTies T n').deg a := by sorry
