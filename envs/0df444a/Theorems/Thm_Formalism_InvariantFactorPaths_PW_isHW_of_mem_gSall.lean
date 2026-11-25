-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_isHW_of_mem_gSall
-- name    : Formalism.InvariantFactorPaths.PW.isHW_of_mem_gSall
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T01:44:50.0664+00:00
-- url     : https://prove2.me/theorems/32ba2cb3-1837-40f7-a596-842b38fe5cd9
-- title:
--   PW: is HW of mem g Sall
-- statement:
--   The PW construction uses the is HW of mem g Sall property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L43-L52
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/CompEqZeroOfNotDle.lean#L43-L52

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

theorem Formalism.InvariantFactorPaths.PW.isHW_of_mem_gSall {μ : Fin n → ℤ} {x : V} (hx : x ∈ G.gS {v | G.IsHW μ v}) (hw : G.IsWt μ x) :
    G.IsHW μ x := by sorry
