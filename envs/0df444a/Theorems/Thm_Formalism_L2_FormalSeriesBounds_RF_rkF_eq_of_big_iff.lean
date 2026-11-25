-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_rkF_eq_of_big_iff
-- name    : Formalism.L2.FormalSeriesBounds.RF.rkF_eq_of_big_iff
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T00:14:05.223151+00:00
-- url     : https://prove2.me/theorems/03805d7f-fc90-4013-93a6-114a69024d1f
-- title:
--   RF: rk F eq of big iff
-- statement:
--   The RF construction uses the rk F eq of big iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L152-L156
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L152-L156

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
variable {X F}

theorem Formalism.L2.FormalSeriesBounds.RF.rkF_eq_of_big_iff {g g' : Fin 2} {a a' : ZMod d} (h : X.big g a ↔ X.big g' a') : X.rkF g a = X.rkF g' a' := by sorry
