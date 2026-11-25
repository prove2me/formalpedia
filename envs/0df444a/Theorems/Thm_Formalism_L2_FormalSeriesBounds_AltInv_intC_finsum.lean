-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_AltInv_intC_finsum
-- name    : Formalism.L2.FormalSeriesBounds.AltInv.intC_finsum
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:19:35.223802+00:00
-- url     : https://prove2.me/theorems/0a287b0c-5447-4bc4-b38c-19c7d4a1346a
-- title:
--   Alt Inv: int C finsum
-- statement:
--   The Alt Inv construction uses the int C finsum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L58-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/AltInv.lean#L58-L63

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_AltInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.AltInv
variable {C : Type*} [Field C] (v : AddValuation C (WithTop ℝ))
variable {v}

theorem Formalism.L2.FormalSeriesBounds.AltInv.intC_finsum {ι : Type*} {f : ι → C} (h : ∀ i, IntC v (f i)) : IntC v (∑ᶠ i, f i) := by sorry
