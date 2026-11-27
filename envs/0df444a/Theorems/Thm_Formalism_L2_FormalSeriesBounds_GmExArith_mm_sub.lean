-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_sub
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.mm_sub
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-27T05:35:05.336963+00:00
-- url     : https://prove2.me/theorems/033a4ef5-9d6a-51f3-85eb-a2ac4451b7c0
-- title:
--   Gm Ex Arith: mm sub
-- statement:
--   The Gm Ex Arith construction uses the mm sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L25-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L25-L26

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.mm_sub {a b : C} (ha : V.MM a) (hb : V.MM b) : V.MM (a - b) := by sorry
