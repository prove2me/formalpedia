-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_int_mul
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.mm_int_mul
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-27T05:07:42.70985+00:00
-- url     : https://prove2.me/theorems/9953f46d-7153-5c2c-9505-530fdbcdb23b
-- title:
--   Gm Ex Arith: mm int mul
-- statement:
--   The Gm Ex Arith construction uses the mm int mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L37-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L37-L38

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.mm_int_mul {a b : C} (ha : V.Ge 0 a) (hb : V.MM b) : V.MM (a * b) := by sorry
