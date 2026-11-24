-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_intPol_zpClosed
-- name    : Formalism.InvariantFactorPaths.PW.intPol_zpClosed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:22.418568+00:00
-- url     : https://prove2.me/theorems/71ffd817-efc8-47d1-a381-453de99c82f4
-- title:
--   PW: int Pol zp Closed
-- statement:
--   The PW construction uses the int Pol zp Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L14-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L14-L19

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

theorem Formalism.InvariantFactorPaths.PW.intPol_zpClosed (σ : Type) : ZpClosed p (IntPol p σ).toAddSubgroup := by sorry
