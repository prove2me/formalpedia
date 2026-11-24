-- Prove2me | Theorems.Thm_Formalism_GM_levelAct_of
-- name    : Formalism.GM.levelAct_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:35.091922+00:00
-- url     : https://prove2.me/theorems/37566298-271b-4d14-b2e6-d8a5a89ecc6b
-- title:
--   GM: level Act of
-- statement:
--   The GM construction uses the level Act of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L243-L279
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LevelAct.lean#L243-L279

import Definitions.Def_Formalism_MahlerMeasure_LevelSum
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LevelAct
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open MvPolynomial Finset

theorem Formalism.GM.levelAct_of (hS : LevelSum) : LevelAct := by sorry
