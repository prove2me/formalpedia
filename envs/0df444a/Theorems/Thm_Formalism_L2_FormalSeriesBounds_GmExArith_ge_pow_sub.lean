-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_ge_pow_sub
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.ge_pow_sub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-27T05:08:25.537706+00:00
-- url     : https://prove2.me/theorems/46c0a9d9-26f8-5d8f-98cc-2dafd53ac0eb
-- title:
--   Gm Ex Arith: ge pow sub
-- statement:
--   The Gm Ex Arith construction uses the ge pow sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L154-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L154-L156

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.ge_pow_sub {A B : C} (hA : V.Ge 0 A) (hB : V.Ge 0 B) {w : ℝ} (h : V.Ge w (A - B)) (n : ℕ) :
    V.Ge w (A ^ n - B ^ n) := by sorry
