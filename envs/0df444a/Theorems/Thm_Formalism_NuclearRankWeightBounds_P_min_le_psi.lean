-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_min_le_psi
-- name    : Formalism.NuclearRankWeightBounds.P.min_le_psi
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:25.480173+00:00
-- url     : https://prove2.me/theorems/c0eabf1a-f85e-4eb7-b54f-790d7307e36a
-- title:
--   P: min le psi
-- statement:
--   The P construction uses the min le psi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L49-L89
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L49-L89

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

theorem Formalism.NuclearRankWeightBounds.P.min_le_psi (x y r : ℝ) (hx : 0 < x) (hy : 0 < y) (hr : |r| ≤ y) :
    (min 1 (x / y)) ^ (5 / 4 : ℝ) ≤ psi ⌊2 * r / x⌋ := by sorry
