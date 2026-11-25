-- Prove2me | Theorems.Thm_Formalism_GM_semisimple_direct_sum
-- name    : Formalism.GM.semisimple_direct_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:55:34.904567+00:00
-- url     : https://prove2.me/theorems/48d3d952-1421-4a7a-98df-c731f8f17fde
-- title:
--   GM: semisimple direct sum
-- statement:
--   The GM construction uses the semisimple direct sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L786-L788
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/SSDirect.lean#L786-L788

import Definitions.Def_Formalism_MahlerMeasure_LevelLattice
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_SSDirect
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM

theorem Formalism.GM.semisimple_direct_sum : Formalism.GM.M.SSDirect := by sorry
