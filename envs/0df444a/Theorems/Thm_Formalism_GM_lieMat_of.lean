-- Prove2me | Theorems.Thm_Formalism_GM_lieMat_of
-- name    : Formalism.GM.lieMat_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:40.578602+00:00
-- url     : https://prove2.me/theorems/769c258c-0feb-402f-b502-6ac112d43f30
-- title:
--   GM: lie Mat of
-- statement:
--   The GM construction uses the lie Mat of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L125-L224
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/LieMat.lean#L125-L224

import Definitions.Def_Formalism_MahlerMeasure_LieRoots
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_LieMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial DetBound

theorem Formalism.GM.lieMat_of (hM : MahlerK) : LieMat := by sorry
