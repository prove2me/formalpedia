-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_gSall_le_iSup
-- name    : Formalism.InvariantFactorPaths.PW.gSall_le_iSup
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T01:33:45.656324+00:00
-- url     : https://prove2.me/theorems/be56ffcd-2cd0-42c0-9fa1-96dfd1b5336f
-- title:
--   PW: g Sall le i Sup
-- statement:
--   The PW construction uses the g Sall le i Sup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L12-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L12-L32

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_OrthogonalIsomorphismHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CommProjectionHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_CompEqZeroOfNotDle
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
variable {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] {n : ℕ} (G : GlW K V n)

theorem Formalism.InvariantFactorPaths.PW.gSall_le_iSup (μ : Fin n → ℤ) :
    G.gS {v | G.IsHW μ v} ≤ ⨆ v : {v // G.IsHW μ v}, G.gS {v.1} := by sorry
