-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_v_eq_zero_of
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.v_eq_zero_of
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-27T05:27:00.370258+00:00
-- url     : https://prove2.me/theorems/c70954de-e4a7-5be6-ad54-e369a85f9e6e
-- title:
--   Gm Ex Arith: v eq zero of
-- statement:
--   The Gm Ex Arith construction uses the v eq zero of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L60-L61

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.v_eq_zero_of {a : C} (h0 : V.Ge 0 a) (h : ¬ V.MM a) : V.v a = 0 := by sorry
