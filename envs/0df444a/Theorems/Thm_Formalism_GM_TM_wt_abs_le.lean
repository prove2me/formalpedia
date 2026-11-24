-- Prove2me | Theorems.Thm_Formalism_GM_TM_wt_abs_le
-- name    : Formalism.GM.TM.wt_abs_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:02.489788+00:00
-- url     : https://prove2.me/theorems/ef7c7637-55de-42a8-8fa1-54754f6561e6
-- title:
--   TM: wt abs le
-- statement:
--   The TM construction uses the wt abs le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L134-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/TheoremM.lean#L134-L142

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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.GM.TM.wt_abs_le {N r : ℕ} (LL : Letters N) (j : ℕ) (c : Fin r) (m : Fin N × Fin r →₀ ℕ) (hm : MultiDeg LL m) :
    |wt LL j c m| ≤ (LL.total : ℤ) := by sorry
