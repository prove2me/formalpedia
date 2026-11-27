-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_pow
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.mm_pow
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:18:16.713813+00:00
-- url     : https://prove2.me/theorems/3b95b297-0b3a-5a24-8e6b-e854214afad4
-- title:
--   Gm Ex Arith: mm pow
-- statement:
--   The Gm Ex Arith construction uses the mm pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L49-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L49-L51

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.mm_pow {a : C} (h : V.MM a) {n : ℕ} (hn : n ≠ 0) : V.MM (a ^ n) := by sorry
