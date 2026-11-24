-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_OrbitRepresentatives_exists_reps
-- name    : Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.exists_reps
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:39:27.524802+00:00
-- url     : https://prove2.me/theorems/ecdbbc5b-70ce-4af3-a2ff-2d7c9674c374
-- title:
--   Orbit Representatives: exists reps
-- statement:
--   The Orbit Representatives construction uses the exists reps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardStabilizerAutSub.lean#L76-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardStabilizerAutSub.lean#L76-L117

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomMapOfEq
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AdjoinMemGenusIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FiniteRepSetOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardStabilizerAutSub
import Theorems.Thm_Formalism_ThetaLiftIndependence_DefiniteClassRepresentatives_exists_reps

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.OrbitRepresentatives.exists_reps (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) {h : V →ₗ⋆[K] V →ₗ[K] K}
    (hs : h.IsSymm) {I : Submodule (𝓞 K) V} {n : ℕ} (hI : Formalism.HermitianLatticesTheory.IsOrthoLattice h I n)
    {L : Submodule (𝓞 K) V} (hL : Submodule.IsLattice K L) :
    ∃ T : Finset V, (∀ t ∈ T, t ∈ L ∧ h t t = 1) ∧
      (∀ x, x ∈ L → h x x = 1 → ∃ t ∈ T, ∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t = x) ∧
      (∀ t₁ ∈ T, ∀ t₂ ∈ T, (∃ a ∈ Formalism.ThetaLiftIndependence.autL h L, a t₁ = t₂) → t₁ = t₂) ∧
      (repCount h L 1 : ℝ) / ((Nat.card (Formalism.ThetaLiftIndependence.autL h L) : ℕ) : ℝ) =
        ∑ t ∈ T, ((Nat.card {g : V ≃ₗ[K] V // g ∈ Formalism.ThetaLiftIndependence.autL h L ∧ g t = t} : ℕ) : ℝ)⁻¹ := by sorry
