-- Prove2me | Theorems.Thm_Formalism_L2_PairingIndexBounds_Mv_Xi_of_eq_sum
-- name    : Formalism.L2.PairingIndexBounds.Mv.Xi_of_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:15:30.785386+00:00
-- url     : https://prove2.me/theorems/0ce8ec37-5826-4587-ac2b-c794f3f9bcc5
-- title:
--   Mv: Xi of eq sum
-- statement:
--   The Mv construction uses the Xi of eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L408-L421
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/PairingIndexBounds/ModelLatticeMoves/ModelIndexPairings/FourierTransformIdentityHolds.lean#L408-L421

import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelMoves
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_ModelLatticeMoves_ModelIndexPairings_FourierTransformIdentityHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Mv
variable {k : Type*} [Field k] {A B T : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup T] [Module k T]

theorem Formalism.L2.PairingIndexBounds.Mv.Xi_of_eq_sum {c : B → A → k} {WA : A → T →ₗ[k] T} {WB : B → T →ₗ[k] T} {A₀ : AddSubgroup A} {θ : T}
    {Xi : Sch c A₀ →ₗ[k] T} (hXi : IsXi c WA WB A₀ θ Xi) {ι : Type*} (s : Finset ι) (r : ι → k) (a : ι → A)
    (b : ι → B) (Φ : A → k) (hΦ : Φ = ∑ i ∈ s, r i • gen c A₀ (a i) (b i)) :
    ∃ h : Φ ∈ Sch c A₀, Xi ⟨Φ, h⟩ = ∑ i ∈ s, r i • WA (a i) (WB (b i) θ) := by sorry
