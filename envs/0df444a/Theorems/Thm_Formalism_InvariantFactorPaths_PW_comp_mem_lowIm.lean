-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_comp_mem_lowIm
-- name    : Formalism.InvariantFactorPaths.PW.comp_mem_lowIm
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T01:33:14.84782+00:00
-- url     : https://prove2.me/theorems/01509ae0-1f55-4884-bb30-c34f0d4a7118
-- title:
--   PW: comp mem low Im
-- statement:
--   The PW construction uses the comp mem low Im property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L56-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L56-L67

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

theorem Formalism.InvariantFactorPaths.PW.comp_mem_lowIm {μ ν : Fin n → ℤ} (hne : μ ≠ ν) {x : V} (hx : x ∈ G.gS {v | G.IsHW ν v}) :
    G.comp μ x ∈ lowIm G := by sorry
