-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_exists_rowsOK
-- name    : Formalism.L2.FormalSeriesBounds.RF.exists_rowsOK
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T00:46:56.10857+00:00
-- url     : https://prove2.me/theorems/d692b1fe-3250-4ac8-8ea0-2c76fce22c58
-- title:
--   RF: exists rows OK
-- statement:
--   The RF construction uses the exists rows OK property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L58-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/FinTwoNeOneSub.lean#L58-L108

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_FinTwoNeOneSub
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
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C] {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)] [∀ g, Fintype (J g)]
variable (X : RowData C V d I J) (F : Flag X)

theorem Formalism.L2.FormalSeriesBounds.RF.exists_rowsOK (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) :
    ∃ kind : Fin (b.what₂ X.n) → Knd d, RowsOK X.G X.Alt (b.poly X F) kind := by sorry
