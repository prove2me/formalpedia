-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_hom_eig_zero
-- name    : Formalism.InvariantFactorPaths.PW.hom_eig_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:16.629299+00:00
-- url     : https://prove2.me/theorems/ee1a55d0-d38b-4073-99b1-e799bbbbf946
-- title:
--   PW: hom eig zero
-- statement:
--   The PW construction uses the hom eig zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/SchurTraceOfHomInv.lean#L27-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/SchurTraceOfHomInv.lean#L27-L60

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.PW
open Finset Formalism.GM.DimensionMonotonicity
variable {K V V₁ V₂ : Type} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V₁] [Module K V₁]
  [AddCommGroup V₂] [Module K V₂] {n : ℕ}

theorem Formalism.InvariantFactorPaths.PW.hom_eig_zero [CharZero K] (G₁ : GlW K V₁ n) (G₂ : GlW K V₂ n) (W : Submodule K V₂) (l : ℕ)
    (hW : G₂.Stable W) (hb : WtBound2 G₁ G₂ W l) (z : Fin n) (k : ℤ) (φ : V₁ →ₗ[K] V₂) (hφ : ∀ x, φ x ∈ W)
    (he : homAct G₁.E G₂.E z z φ = (k : K) • φ) (hk : (l : ℤ) < |k|) : φ = 0 := by sorry
