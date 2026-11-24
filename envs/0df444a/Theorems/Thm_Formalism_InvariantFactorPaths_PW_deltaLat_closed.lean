-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_deltaLat_closed
-- name    : Formalism.InvariantFactorPaths.PW.deltaLat_closed
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:24.86281+00:00
-- url     : https://prove2.me/theorems/fdc12111-35f5-4c76-97d0-2b5bfd80aeb2
-- title:
--   PW: delta Lat closed
-- statement:
--   The PW construction uses the delta Lat closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L138-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L138-L141

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

theorem Formalism.InvariantFactorPaths.PW.deltaLat_closed (G : GlW ℚ_[p] V n) (s : Set V) : ZpClosed p (DeltaLat p G s) := by sorry
