-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_exp_ge_quad
-- name    : Formalism.NuclearRankWeightBounds.P.exp_ge_quad
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:13.653836+00:00
-- url     : https://prove2.me/theorems/a6bd2959-a4bb-457e-b587-c61c11dd9ae8
-- title:
--   P: exp ge quad
-- statement:
--   The P construction uses the exp ge quad property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LogSumExpBoundHolds.lean#L7-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LogSumExpBoundHolds.lean#L7-L20

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LogSumExpBoundHolds
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

theorem Formalism.NuclearRankWeightBounds.P.exp_ge_quad {z : ℝ} (hz : |z| ≤ 1) : 1 + z + z ^ 2 / 3 ≤ Real.exp z := by sorry
