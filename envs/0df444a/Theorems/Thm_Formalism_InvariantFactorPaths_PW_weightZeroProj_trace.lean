-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_trace
-- name    : Formalism.InvariantFactorPaths.PW.weightZeroProj_trace
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:04.333313+00:00
-- url     : https://prove2.me/theorems/24fad054-9edb-4935-a5f2-72aead7c9aab
-- title:
--   PW: weight Zero Proj trace
-- statement:
--   The PW construction uses the weight Zero Proj trace property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L71-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L71-L90

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
variable {K U V : Type} [Field K] [CharZero K] [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] {n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.weightZeroProj_trace (G₁ : GlW K U n) (S : Finset (Fin n → ℤ)) (hS : ∀ x, ∀ μ ∉ S, G₁.comp μ x = 0) (φ : U →ₗ[K] U) :
    LinearMap.trace K U (pr0 G₁ G₁ S φ) = LinearMap.trace K U φ := by sorry
