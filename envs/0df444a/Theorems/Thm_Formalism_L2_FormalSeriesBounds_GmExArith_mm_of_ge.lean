-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_mm_of_ge
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.mm_of_ge
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-27T05:10:48.373826+00:00
-- url     : https://prove2.me/theorems/079bb3d1-4221-5794-a67a-6ca4be355650
-- title:
--   Gm Ex Arith: mm of ge
-- statement:
--   The Gm Ex Arith construction uses the mm of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L46-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L46-L47

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.mm_of_ge {ε : ℝ} (hε : 0 < ε) {a : C} (h : V.Ge ε a) : V.MM a := by sorry
