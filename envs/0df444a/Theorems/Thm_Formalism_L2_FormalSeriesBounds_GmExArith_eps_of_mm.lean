-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_eps_of_mm
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.eps_of_mm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:18:43.565806+00:00
-- url     : https://prove2.me/theorems/7d5975a7-4887-5ac2-a01c-92374d832da9
-- title:
--   Gm Ex Arith: eps of mm
-- statement:
--   The Gm Ex Arith construction uses the eps of mm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L229-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L229-L246

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.eps_of_mm {ι : Type} [Finite ι] (f : ι → C) (h : ∀ i, V.MM (f i)) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ i, V.Ge ε (f i) := by sorry
