-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpS
-- name    : Formalism.InvariantFactorPaths.PW.mem_perpS
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:06:36.552881+00:00
-- url     : https://prove2.me/theorems/b710b047-643f-4146-b231-a8525e103df0
-- title:
--   PW: mem perp S
-- statement:
--   The PW construction uses the mem perp S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L36-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L36-L37

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Formalism.GM.M Formalism.GM.DimensionMonotonicity MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.PW.mem_perpS (A : Submodule ℚ_[p] (MvPolynomial σ ℚ_[p])) (y : MvPolynomial σ ℚ_[p]) :
    y ∈ perpS A ↔ ∀ x ∈ A, fock p x y = 0 := by sorry
