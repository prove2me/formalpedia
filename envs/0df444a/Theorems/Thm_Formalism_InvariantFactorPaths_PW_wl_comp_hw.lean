-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_comp_hw
-- name    : Formalism.InvariantFactorPaths.PW.wl_comp_hw
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:36.842273+00:00
-- url     : https://prove2.me/theorems/dab33164-2176-40b2-b6a4-32f88d2caf35
-- title:
--   PW: wl comp hw
-- statement:
--   The PW construction uses the wl comp hw property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L39-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L39-L47

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
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

theorem Formalism.InvariantFactorPaths.PW.wl_comp_hw (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) {x : V} (hx : x ∈ IsoW G W la) :
    G.IsHW la (G.comp la x) := by sorry
