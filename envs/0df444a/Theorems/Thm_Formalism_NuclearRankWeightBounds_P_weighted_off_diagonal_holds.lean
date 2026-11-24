-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_weighted_off_diagonal_holds
-- name    : Formalism.NuclearRankWeightBounds.P.weighted_off_diagonal_holds
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T10:17:46.540442+00:00
-- url     : https://prove2.me/theorems/025553f4-96ad-4f04-ae47-51ae449f4ef7
-- title:
--   P: weighted off diagonal holds
-- statement:
--   The P construction uses the weighted off diagonal holds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/WeightedOffDiagonalHolds.lean#L7-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/WeightedOffDiagonalHolds.lean#L7-L75

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_WeightedOffDiagonalHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset Formalism.NuclearRankWeightBounds.D

theorem Formalism.NuclearRankWeightBounds.P.weighted_off_diagonal_holds : Formalism.NuclearRankWeightBounds.D.WeightedOff := by sorry
