-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_equiv_zero
-- name    : Formalism.InvariantFactorPaths.PW.equiv_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:23.538212+00:00
-- url     : https://prove2.me/theorems/7cf4edf9-58f8-4153-b316-5ef3298a5a71
-- title:
--   PW: equiv zero
-- statement:
--   The PW construction uses the equiv zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L248-L265
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/TypeInt.lean#L248-L265

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_StatementB
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_HomRelationHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_TypeInt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_subset_gS

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

theorem Formalism.InvariantFactorPaths.PW.equiv_zero (G : GlW K V n) (h : V) (ψ : G.gS {h} →ₗ[K] V)
    (hψ : ∀ a b x, ψ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (ψ x))
    (h0 : ψ ⟨h, G.subset_gS _ (Set.mem_singleton h)⟩ = 0) : ψ = 0 := by sorry
