-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_hw_IsoW_zero
-- name    : Formalism.InvariantFactorPaths.PW.hw_IsoW_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:07.376602+00:00
-- url     : https://prove2.me/theorems/ae3d6a02-9ac4-4af6-afd0-1a1bdbb6cc90
-- title:
--   PW: hw Iso W zero
-- statement:
--   The PW construction uses the hw Iso W zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L200-L246
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L200-L246

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity Formalism.CountingSumsFrames
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.hw_IsoW_zero (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la mu : Fin n → ℤ}
    (hne : mu ≠ la) {x : V} (hx : G.IsHW la x) (hxI : x ∈ IsoW G W mu) : x = 0 := by sorry
