-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_pol_le_iSup
-- name    : Formalism.InvariantFactorPaths.PW.pol_le_iSup
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:09:05.370132+00:00
-- url     : https://prove2.me/theorems/89ccba01-cc63-4261-9dc4-0c0f625c1838
-- title:
--   PW: pol le i Sup
-- statement:
--   The PW construction uses the pol le i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L147-L161
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/OrthogonalIsomorphismHolds.lean#L147-L161

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

theorem Formalism.InvariantFactorPaths.PW.pol_le_iSup (LL L2 : Letters N) (j : ℕ) (Cs : Finset (Fin r)) :
    Pol p r L2 ≤ ⨆ la : Fin r → ℤ, IsoC p LL j Cs la := by sorry
