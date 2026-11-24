-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_weightZeroProj_mem_homLat
-- name    : Formalism.InvariantFactorPaths.PW.weightZeroProj_mem_homLat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:25.778722+00:00
-- url     : https://prove2.me/theorems/f85607b1-f3b5-4d4e-b37a-4b68e9d73e24
-- title:
--   PW: weight Zero Proj mem hom Lat
-- statement:
--   The PW construction uses the weight Zero Proj mem hom Lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L40-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L40-L47

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

theorem Formalism.InvariantFactorPaths.PW.weightZeroProj_mem_homLat (G₁ : GlW K U n) (G₂ : GlW K V n) (S : Finset (Fin n → ℤ)) {L : AddSubgroup U} {M : AddSubgroup V}
    (hL : ∀ μ, ∀ x ∈ L, G₁.comp μ x ∈ L) (hM : ∀ μ, ∀ x ∈ M, G₂.comp μ x ∈ M)
    {φ : U →ₗ[K] V} (hφ : φ ∈ HomLat (K := K) L M) : pr0 G₁ G₂ S φ ∈ HomLat (K := K) L M := by sorry
