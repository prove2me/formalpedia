-- Prove2me | Theorems.Thm_Formalism_IrreducibleCountingLemmas_TW_unit_ball_is_lattice
-- name    : Formalism.IrreducibleCountingLemmas.TW.unit_ball_is_lattice
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:05.818436+00:00
-- url     : https://prove2.me/theorems/fa0480ff-e4e9-48bc-8a74-3a75da9a6688
-- title:
--   TW: unit ball is lattice
-- statement:
--   The TW construction uses the unit ball is lattice property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWUnitBallLattice.lean#L81-L170
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PadicSubsetSums/StableGradedCounts/TWUnitBallLattice.lean#L81-L170

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
open UnitBall

theorem Formalism.IrreducibleCountingLemmas.TW.unit_ball_is_lattice : UnitBallLattice := by sorry
