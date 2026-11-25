-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_attainsOK_of
-- name    : Formalism.L2.FormalSeriesBounds.RF.attainsOK_of
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:14:48.284568+00:00
-- url     : https://prove2.me/theorems/29ecd0d8-e371-4618-8431-b17d53da5faf
-- title:
--   RF: attains OK of
-- statement:
--   The RF construction uses the attains OK of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L82-L139
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieAdm.lean#L82-L139

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

theorem Formalism.L2.FormalSeriesBounds.RF.attainsOK_of (hdich : X.Alt ∨ ∀ a, X.big 0 a) (hj : X.j' < X.n) (b : GlobalTheory d) (c : ℝ)
    (hwt : ∀ g a k, b.wt X g a k ≠ 0 → k ≤ X.rkF g a) (h : b.Attains X F c) : b.AttainsOK X F c := by sorry
