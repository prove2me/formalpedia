-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_cell_sum_le
-- name    : Formalism.NuclearRankWeightBounds.P.cell_sum_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T10:18:13.555356+00:00
-- url     : https://prove2.me/theorems/bdeb8633-8f55-474d-a5d1-d62505ba65ef
-- title:
--   P: cell sum le
-- statement:
--   The P construction uses the cell sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L91-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L91-L124

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

theorem Formalism.NuclearRankWeightBounds.P.cell_sum_le (f : ℕ) (P : Finset (Fin f → ℤ × ℤ)) :
    ∑ p ∈ P, ∏ v, (psi (p v).1 * psi (p v).2) ≤ ((∑' n, psi n) ^ 2) ^ f := by sorry
