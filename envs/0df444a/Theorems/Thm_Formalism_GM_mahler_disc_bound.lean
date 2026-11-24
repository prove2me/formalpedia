-- Prove2me | Theorems.Thm_Formalism_GM_mahler_disc_bound
-- name    : Formalism.GM.mahler_disc_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:41.105437+00:00
-- url     : https://prove2.me/theorems/f46c79d4-422d-41d9-b325-cb251cb9ca9b
-- title:
--   GM: mahler disc bound
-- statement:
--   The GM construction uses the mahler disc bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L149-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/Mahler.lean#L149-L152

import Definitions.Def_Formalism_MahlerMeasure_StatementB
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_Mahler
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Polynomial

theorem Formalism.GM.mahler_disc_bound : MahlerDisc := by sorry
