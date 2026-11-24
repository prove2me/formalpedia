-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_UnitBall_ballRing_pid
-- name    : Formalism.IrreducibleCountingLemmas.TW.UnitBall.ballRing_pid
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:24.458354+00:00
-- url     : https://prove2.me/theorems/4bd3f94e-82a9-42b4-9556-9b28a5cc0ca2
-- title:
--   Unit Ball: ball Ring pid
-- statement:
--   The Unit Ball construction uses the ball Ring pid property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWUnitBallLattice.lean#L45-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWUnitBallLattice.lean#L45-L75

import Mathlib
import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_CentralIdempotentIntegral
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_TWUnitBallLattice
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.TW
open Formalism.IrreducibleCountingLemmas.TW.UnitBall
variable {K : Type} [NontriviallyNormedField K] [IsUltrametricDist K]

theorem Formalism.IrreducibleCountingLemmas.TW.UnitBall.ballRing_pid (ϖ : K) (h1 : ‖ϖ‖ < 1) (hd : ∀ x : K, x ≠ 0 → ∃ n : ℤ, ‖x‖ = ‖ϖ‖ ^ n) :
    IsPrincipalIdealRing (ballRing K) := by sorry
