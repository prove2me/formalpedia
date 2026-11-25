-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_sz_nonneg
-- name    : Formalism.NuclearRankWeightBounds.P.sz_nonneg
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:51:49.29581+00:00
-- url     : https://prove2.me/theorems/da5dbb30-5216-522f-8d4d-1bba7c69e4fe
-- title:
--   P: sz nonneg
-- statement:
--   The P construction uses the sz nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/ZLiftAsm.lean#L10-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/ZLiftAsm.lean#L10-L15

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_ZLiftAsm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset

theorem Formalism.NuclearRankWeightBounds.P.sz_nonneg {f : ℕ} (x : Fin f → ℝ) (K : ℕ) (z : Fin f → ℂ) (a : ℝ) (hx : ∀ v, 0 < x v) :
    0 ≤ sz x K z a := by sorry
