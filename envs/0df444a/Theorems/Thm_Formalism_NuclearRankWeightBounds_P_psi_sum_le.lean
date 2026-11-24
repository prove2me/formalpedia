-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_psi_sum_le
-- name    : Formalism.NuclearRankWeightBounds.P.psi_sum_le
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:45.946845+00:00
-- url     : https://prove2.me/theorems/f3e0aa75-70f3-44ff-bc9b-91c4e99e7a7a
-- title:
--   P: psi sum le
-- statement:
--   The P construction uses the psi sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L31-L32

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

theorem Formalism.NuclearRankWeightBounds.P.psi_sum_le (T : Finset ℤ) : ∑ n ∈ T, psi n ≤ ∑' n, psi n := by sorry
