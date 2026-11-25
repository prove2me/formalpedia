-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_vV_algebraMap_nonneg
-- name    : Formalism.L2.FormalSeriesBounds.vV_algebraMap_nonneg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:24:51.218823+00:00
-- url     : https://prove2.me/theorems/64e7c6ec-10c0-4a78-a181-0620ae007e1b
-- title:
--   Formal Series Bounds: v V algebra Map nonneg
-- statement:
--   The Formal Series Bounds construction uses the v V algebra Map nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePEmbIntSt.lean#L11-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePEmbIntSt.lean#L11-L22

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieCuts
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePEmbIntSt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.vV_algebraMap_nonneg (T : CDVR) (t : T.V) : 0 ≤ vV T.V (algebraMap T.V T.Fr t) := by sorry
