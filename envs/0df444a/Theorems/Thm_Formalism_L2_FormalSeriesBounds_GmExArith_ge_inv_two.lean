-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_GmExArith_ge_inv_two
-- name    : Formalism.L2.FormalSeriesBounds.GmExArith.ge_inv_two
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-27T05:17:57.011377+00:00
-- url     : https://prove2.me/theorems/c6fe078b-971c-4299-99a6-904421ade7fb
-- title:
--   Gm Ex Arith: ge inv two
-- statement:
--   The Gm Ex Arith construction uses the ge inv two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L129-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePGmExLem.lean#L129-L148

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

theorem Formalism.L2.FormalSeriesBounds.GmExArith.ge_inv_two [CharZero C] (hl2 : V.l ≠ 2) : V.Ge 0 ((2 : C)⁻¹) := by sorry
