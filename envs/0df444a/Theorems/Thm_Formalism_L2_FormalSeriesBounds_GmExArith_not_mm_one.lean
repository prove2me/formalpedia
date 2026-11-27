-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_not_mm_one
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.not_mm_one
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-27T05:14:03.575563+00:00
-- url     : https://prove2.me/theorems/28bcce8b-c8a6-535c-bde5-32ca27647fb4
-- title:
--   Gm Ex Arith: not mm one
-- statement:
--   The Gm Ex Arith construction uses the not mm one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L43-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L43-L44

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_SelfConjugateRowData
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePGmExLem
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
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.GmExArith
open Formalism.L2.FormalSeriesBounds NumberField
variable {C : Type} [Field C] {V : VF C}

theorem Formalism.L2.FormalSeriesBounds.GmExArith.not_mm_one : ¬ V.MM (1 : C) := by sorry
