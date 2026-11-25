-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_HaP_exists_clear
-- name    : Formalism.L2.FormalSeriesBounds.HaP.exists_clear
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T00:46:44.781856+00:00
-- url     : https://prove2.me/theorems/460052ee-1deb-4f05-bf04-41da96a7dcde
-- title:
--   Ha P: exists clear
-- statement:
--   The Ha P construction uses the exists clear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L239-L247
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/RowTiePHaSpan.lean#L239-L247

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaDefs
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePDescSpanSt
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePHaSpan
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
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.HaP
open MvPolynomial Formalism.L2.Pj

theorem Formalism.L2.FormalSeriesBounds.HaP.exists_clear (s : Type) [Fintype s] (u : s → ℚ) :
    ∃ N : ℕ, N ≠ 0 ∧ ∃ z : s → ℤ, ∀ b, (z b : ℚ) = N * u b := by sorry
