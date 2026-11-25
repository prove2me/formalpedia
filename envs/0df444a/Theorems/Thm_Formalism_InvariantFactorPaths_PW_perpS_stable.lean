-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_perpS_stable
-- name    : Formalism.InvariantFactorPaths.PW.perpS_stable
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:09:02.269315+00:00
-- url     : https://prove2.me/theorems/cb8a1c21-8d3f-4fdb-b7b2-4e78338b3aaf
-- title:
--   PW: perp S stable
-- statement:
--   The PW construction uses the perp S stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L219-L228
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L219-L228

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
variable {p : ℕ} [Fact p.Prime] {N r n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.perpS_stable (LL : Letters N) (j : ℕ) (e : Fin n ↪o Fin r)
    {A : Submodule ℚ_[p] (MvPolynomial (Fin N × Fin r) ℚ_[p])} (hA : (GAe p LL j e).Stable A) :
    (GAe p LL j e).Stable (perpS A) := by sorry
