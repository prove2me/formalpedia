-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_tsum_psi_nonneg
-- name    : Formalism.NuclearRankWeightBounds.P.tsum_psi_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:41.605166+00:00
-- url     : https://prove2.me/theorems/e63775ab-6e97-4e39-a54b-e274707c368c
-- title:
--   P: tsum psi nonneg
-- statement:
--   The P construction uses the tsum psi nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L34-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/LatSum.lean#L34-L34

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

theorem Formalism.NuclearRankWeightBounds.P.tsum_psi_nonneg : 0 ≤ ∑' n, psi n := by sorry
