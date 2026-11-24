-- Prove2me | Theorems.Thm_Formalism_GM_extendMapsTo
-- name    : Formalism.GM.extendMapsTo
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:33:56.318273+00:00
-- url     : https://prove2.me/theorems/18eb6d80-4648-4ac2-a793-f3c112613177
-- title:
--   GM: extend Maps To
-- statement:
--   The GM construction uses the extend Maps To property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L263-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeInto.lean#L263-L266

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeInto
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM

theorem Formalism.GM.extendMapsTo : M.FreezeInto := by sorry
