-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_big_one_iff
-- name    : Formalism.L2.FormalSeriesBounds.RF.big_one_iff
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:00.433216+00:00
-- url     : https://prove2.me/theorems/7194e010-65f4-4823-a3b4-faf6ca479f5d
-- title:
--   RF: big one iff
-- statement:
--   The RF construction uses the big one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L60-L61
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L60-L61

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipSelfConjugate
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieAdm
import Theorems.Thm_Formalism_BaseCaseIdentities_OrdGE_X

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

theorem Formalism.L2.FormalSeriesBounds.RF.big_one_iff (a : ZMod d) : X.big 1 a ↔ ¬ X.big 0 a := by sorry
