-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_rank_le_of_support
-- name    : Formalism.NuclearRankWeightBounds.P.rank_le_of_support
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:27.150968+00:00
-- url     : https://prove2.me/theorems/da401e2b-633c-437a-9823-614ff9ae64fa
-- title:
--   P: rank le of support
-- statement:
--   The P construction uses the rank le of support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/RankLeOfSupport.lean#L18-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/RankLeOfSupport.lean#L18-L35

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_RankLeOfSupport
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Matrix Finset

theorem Formalism.NuclearRankWeightBounds.P.rank_le_of_support {N : ℕ} (A : Matrix (Fin N) (Fin N) ℂ) (S S' : Finset (Fin N))
    (h : ∀ a b, A a b ≠ 0 → a ∈ S ∧ b ∈ S') : A.rank ≤ min S.card S'.card := by sorry
