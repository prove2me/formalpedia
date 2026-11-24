-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_comp
-- name    : Formalism.InvariantFactorPaths.PW.weightZeroProj_comp
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:37.256668+00:00
-- url     : https://prove2.me/theorems/0ed73125-877d-4b95-a36a-44c773b486bc
-- title:
--   PW: weight Zero Proj comp
-- statement:
--   The PW construction uses the weight Zero Proj comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L65-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L65-L69

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

theorem Formalism.InvariantFactorPaths.PW.weightZeroProj_comp (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) (θ : U →ₗ[K] V)
    (hθ : ∀ μ x, θ (G₁.comp μ x) = G₂.comp μ (θ x)) (φ : U →ₗ[K] U) :
    pr0 G₁ G₂ S (θ ∘ₗ φ) = θ ∘ₗ pr0 G₁ G₁ S φ := by sorry
