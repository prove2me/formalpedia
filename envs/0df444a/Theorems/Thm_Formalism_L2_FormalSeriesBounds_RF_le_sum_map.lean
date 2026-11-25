-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_le_sum_map
-- name    : Formalism.L2.FormalSeriesBounds.RF.le_sum_map
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:43.112497+00:00
-- url     : https://prove2.me/theorems/2cfd1f33-b1ba-4bcc-b1c0-e660cfde2573
-- title:
--   RF: le sum map
-- statement:
--   The RF construction uses the le sum map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L141-L149
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L141-L149

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_sum
import Theorems.Thm_Formalism_L2_FormalSeriesBounds_VF_Ge_sum

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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
  (X : RowData C V d I J) (F : Flag X)

theorem Formalism.L2.FormalSeriesBounds.RF.le_sum_map {α : Type} (l : List α) (f : α → ℕ) {q : α} (hq : q ∈ l) : f q ≤ (l.map f).sum := by sorry
