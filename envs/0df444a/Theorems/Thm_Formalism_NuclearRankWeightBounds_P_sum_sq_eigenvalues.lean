-- Prove2me | Theorems.Thm_Formalism_NuclearRankWeightBounds_P_sum_sq_eigenvalues
-- name    : Formalism.NuclearRankWeightBounds.P.sum_sq_eigenvalues
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:55:41.420795+00:00
-- url     : https://prove2.me/theorems/980f1ceb-9693-4b50-bb89-655b39649fa8
-- title:
--   P: sum sq eigenvalues
-- statement:
--   The P construction uses the sum sq eigenvalues property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/NuclearNormBoundHolds.lean#L7-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LogSumExpBounds/CharacterSumPhase/NuclearNormBoundHolds.lean#L7-L34

import Definitions.Def_Formalism_LogSumExpBounds_NuclearBound
import Definitions.Def_Formalism_LogSumExpBounds_CharacterSumPhase_NuclearNormBoundHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.NuclearRankWeightBounds Formalism.NuclearRankWeightBounds.P
open Finset Matrix

theorem Formalism.NuclearRankWeightBounds.P.sum_sq_eigenvalues {N : ℕ} (Y : Matrix (Fin N) (Fin N) ℂ) (hY : Y.IsHermitian) :
    ∑ j, hY.eigenvalues j ^ 2 = ∑ a, ∑ b, ‖Y a b‖ ^ 2 := by sorry
