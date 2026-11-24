-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_polLatData_of
-- name    : Formalism.InvariantFactorPaths.PW.polLatData_of
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:29:06.172896+00:00
-- url     : https://prove2.me/theorems/ee03e3d5-3ee9-4267-938b-45903b663e7c
-- title:
--   PW: pol Lat Data of
-- statement:
--   The PW construction uses the pol Lat Data of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L32-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L32-L45

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeightCompApply
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_FischerAdjointnessHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_LatData
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
variable {p : ℕ} [Fact p.Prime]

theorem Formalism.InvariantFactorPaths.PW.polLatData_of (hB : LatBasisPol) {p : ℕ} [Fact p.Prime] {N r n : ℕ} (LL L2 : Letters N) (j : ℕ)
    (e : Fin n ↪o Fin r) :
    LatData p (GAe p LL j e) (Pol p r L2) (IntPol p (Fin N × Fin r)).toAddSubgroup L2.total := by sorry
