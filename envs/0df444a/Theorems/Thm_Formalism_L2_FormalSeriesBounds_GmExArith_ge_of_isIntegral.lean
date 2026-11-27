-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_ge_of_isIntegral
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.ge_of_isIntegral
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:11:06.624823+00:00
-- url     : https://prove2.me/theorems/5a21488b-763a-57bc-809b-6ad4ab2b946a
-- title:
--   Gm Ex Arith: ge of is Integral
-- statement:
--   The Gm Ex Arith construction uses the ge of is Integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L92-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L92-L127

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.ge_of_isIntegral {z : C} (hz : IsIntegral ℤ z) : V.Ge 0 z := by sorry
