-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_letter_cast
-- name    : Formalism.L2.FormalSeriesBounds.RF.letter_cast
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-27T05:48:40.254304+00:00
-- url     : https://prove2.me/theorems/656afce5-269b-5e18-9bea-cd0fff69ce03
-- title:
--   RF: letter cast
-- statement:
--   The RF construction uses the letter cast property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCHarm.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTieMemCHarm.lean#L12-L15

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_PderivSubGOff
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTieMemCHarm
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
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial

theorem Formalism.L2.FormalSeriesBounds.RF.letter_cast {T : Type} {r : T → ℕ} {n : ℕ} {σ σ' : T} (h : σ = σ') (a : Fin (r σ)) :
    ∃ a' : Fin (r σ'), ∀ b : Fin n, (⟨σ, a, b⟩ : Letter T r n) = ⟨σ', a', b⟩ := by sorry
