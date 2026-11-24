-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_intPol_whc
-- name    : Formalism.InvariantFactorPaths.PW.intPol_whc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:10.840826+00:00
-- url     : https://prove2.me/theorems/74dbe24d-48ac-4c30-b73e-b1f8bd0b58ab
-- title:
--   PW: int Pol whc
-- statement:
--   The PW construction uses the int Pol whc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L21-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L21-L30

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

theorem Formalism.InvariantFactorPaths.PW.intPol_whc {σ M : Type} [AddCommMonoid M] (w : σ → M) (μ : M) (x : MvPolynomial σ ℚ_[p])
    (hx : x ∈ (IntPol p σ).toAddSubgroup) :
    weightedHomogeneousComponent w μ x ∈ (IntPol p σ).toAddSubgroup := by sorry
