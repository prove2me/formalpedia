-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_PW_wl_key
-- name    : Formalism.InvariantFactorPaths.PW.wl_key
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:42:51.401857+00:00
-- url     : https://prove2.me/theorems/6f699b6f-73ec-4b04-bec4-2a43e0812323
-- title:
--   PW: wl key
-- statement:
--   The PW construction uses the wl key property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L93-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/TraceIsometryWeights/SchurTraceProofs/WeylInt.lean#L93-L125

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

theorem Formalism.InvariantFactorPaths.PW.wl_key (hNat : InvNat) (G : GlW K V n) (W : Submodule K V) (la : Fin n → ℤ) (l : ℕ) {h : V}
    (hh : G.IsHW la h) (h0 : h ≠ 0) [FiniteDimensional K (G.gS {h})]
    (hSch : ∀ φ : (G.gS {h}) →ₗ[K] (G.gS {h}),
      (∀ c, homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E c c φ = 0) →
      InvOp (homAct (res G _ (G.gS_stable {h})).E (res G _ (G.gS_stable {h})).E) l (List.finRange n) φ =
        (LinearMap.trace K _ φ / (Module.finrank K (G.gS {h}) : K)) • LinearMap.id)
    (θ : G.gS {h} →ₗ[K] V) (hθ : ∀ a b x, θ ((res G _ (G.gS_stable {h})).E a b x) = G.E a b (θ x))
    (hθY : ∀ y, θ y ∈ IsoW G W la) (y : G.gS {h}) :
    InvOp (homAct (res G (IsoW G W la) (wl_iso_stable G W la)).E G.E) l (List.finRange n) (topC G W la) ⟨θ y, hθY y⟩ =
      ((Module.finrank K (G.gS {h}) : K))⁻¹ • θ y := by sorry
