-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_mem_intPol_addSubgroup
-- name    : Formalism.InvariantFactorPaths.PW.mem_intPol_addSubgroup
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:39:13.038291+00:00
-- url     : https://prove2.me/theorems/a92377f9-cc43-47f7-b6ec-97aa001de232
-- title:
--   PW: mem int Pol add Subgroup
-- statement:
--   The PW construction uses the mem int Pol add Subgroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L10-L12
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/LatData.lean#L10-L12

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

theorem Formalism.InvariantFactorPaths.PW.mem_intPol_addSubgroup {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ (IntPol p σ).toAddSubgroup ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by sorry
