-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_transport
-- name    : Formalism.InvariantFactorPaths.PW.wl_transport
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:47:13.025087+00:00
-- url     : https://prove2.me/theorems/8fc802b7-3855-4467-a2cd-3a1f5e812c37
-- title:
--   PW: wl transport
-- statement:
--   The PW construction uses the wl transport property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L61-L74
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L61-L74

import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_SchurTraceOfHomInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInv
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_InvInt
import Definitions.Def_Formalism_ThetaLogCoordinates_TraceIsometryWeights_SchurTraceProofs_WeylInt
import Theorems.Thm_Formalism_GM_DimensionMonotonicity_GlW_gS_stable

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

theorem Formalism.InvariantFactorPaths.PW.wl_transport (G : GlW K V n) {W : Submodule K V} (hW : G.Stable W) (hWf : G.FinW W) {la : Fin n → ℤ}
    {h h' : V} (hh : G.IsHW la h) (hh' : G.IsHW la h') (hhW : h ∈ W) (hh'W : h' ∈ W) (h0 : h ≠ 0) :
    ∃ θ : G.gS {h} →ₗ[K] V, (∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x)) ∧
      (∀ y, θ y ∈ G.gS {h'}) ∧ ∀ m ∈ G.gS {h'}, ∃ y, θ y = m := by sorry
