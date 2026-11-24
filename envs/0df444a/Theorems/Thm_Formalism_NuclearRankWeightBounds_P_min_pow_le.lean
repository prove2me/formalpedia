-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_min_pow_le
-- name    : Formalism.NuclearRankWeightBounds.P.min_pow_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:37.454835+00:00
-- url     : https://prove2.me/theorems/e9dee67e-a002-4774-b5bc-33c3530fa39c
-- title:
--   P: min pow le
-- statement:
--   The P construction uses the min pow le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L36-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L36-L47

import Definitions.Def_Formalism_LogSumExpBounds_StatementZ
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
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

theorem Formalism.NuclearRankWeightBounds.P.min_pow_le (t : ℝ) (ht : 0 < t) (K : ℕ) (hK : 3 ≤ K) :
    min 1 (t ^ K) ≤ t ^ ((K : ℝ) - 5 / 2) * ((min 1 t) ^ (5 / 4 : ℝ) * (min 1 t) ^ (5 / 4 : ℝ)) := by sorry
