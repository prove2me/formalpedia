-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_alt_odd_of_big
-- name    : Formalism.L2.FormalSeriesBounds.RF.alt_odd_of_big
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:14:07.572023+00:00
-- url     : https://prove2.me/theorems/dc2744e5-cc56-4dc2-8eda-b9d6a6dd0d32
-- title:
--   RF: alt odd of big
-- statement:
--   The RF construction uses the alt odd of big property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L63-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L63-L80

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

theorem Formalism.L2.FormalSeriesBounds.RF.alt_odd_of_big (hdich : X.Alt ∨ ∀ a, X.big 0 a) {g : Fin 2} {a a' : ZMod d} (h1 : X.big g a)
    (h2 : X.big (1 - g) a') : X.Alt ∧ Odd (a' - a).val := by sorry
