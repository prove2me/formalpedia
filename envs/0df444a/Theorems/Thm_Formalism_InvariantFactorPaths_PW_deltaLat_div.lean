-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_deltaLat_div
-- name    : Formalism.InvariantFactorPaths.PW.deltaLat_div
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:29.650242+00:00
-- url     : https://prove2.me/theorems/7a69fa6f-2050-42b1-8d8d-345618bc2e87
-- title:
--   PW: delta Lat div
-- statement:
--   The PW construction uses the delta Lat div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L143-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L143-L146

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
variable (p : ℕ) [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℚ_[p] V] {n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.deltaLat_div (G : GlW ℚ_[p] V n) (s : Set V) : DivStable G.E (DeltaLat p G s) := by sorry
