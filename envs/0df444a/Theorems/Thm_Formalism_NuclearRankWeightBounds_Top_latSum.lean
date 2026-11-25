-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_Top_latSum
-- name    : Formalism.NuclearRankWeightBounds.Top.latSum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:53:06.937626+00:00
-- url     : https://prove2.me/theorems/f4cbe2d6-15c2-4fd4-85af-beb16c36781e
-- title:
--   Top: lat Sum
-- statement:
--   The Top construction uses the lat Sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/IsoTransfer.lean#L15-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/IsoTransfer.lean#L15-L15

import Definitions.Def_Formalism_LogSumExpBounds_StatementE
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LogSumExpBoundHolds
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_RankLeOfSupport
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_WeightedOffDiagonalHolds
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_KappaModulusHolds
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DetMulDiagonalMulEqSum
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DescEquivLiftEquiv
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_LatSum
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_DecayAsm
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_ZLiftAsm
import Definitions.Def_Formalism_LogSumExpBounds_IsoTransfer
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.Top

theorem Formalism.NuclearRankWeightBounds.Top.latSum : Formalism.NuclearRankWeightBounds.Z.LatSum := by sorry
