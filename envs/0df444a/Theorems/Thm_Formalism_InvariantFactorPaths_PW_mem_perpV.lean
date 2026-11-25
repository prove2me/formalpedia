-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_perpV
-- name    : Formalism.InvariantFactorPaths.PW.mem_perpV
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:08:43.523957+00:00
-- url     : https://prove2.me/theorems/8a81d6b5-3297-4f74-9dc8-0c83736536f3
-- title:
--   PW: mem perp V
-- statement:
--   The PW construction uses the mem perp V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L24-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L24-L24

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

theorem Formalism.InvariantFactorPaths.PW.mem_perpV (h x : MvPolynomial σ ℚ_[p]) : x ∈ perpV h ↔ fock p x h = 0 := by sorry
