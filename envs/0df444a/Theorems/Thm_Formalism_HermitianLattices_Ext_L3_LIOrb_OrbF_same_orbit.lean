-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_OrbF_same_orbit
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.same_orbit
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T08:08:02.968473+00:00
-- url     : https://prove2.me/theorems/07662b1a-fc7a-47a9-8e76-67b497a5a0eb
-- title:
--   Orb F: same orbit
-- statement:
--   The Orb F construction uses the same orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AutSubApplyMem.lean#L67-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/AutSubApplyMem.lean#L67-L105

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ConjMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_AutSubApplyMem
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Filter
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {V' : Type} [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] [Module (𝓞 K) V']
  [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.OrbF.same_orbit (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm) (hd : IsTotPosDef h)
    (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F} (hn : n ≠ 0) (hx : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {g₁ g₂ : V ≃ₗ[K] V} (hg₁ : g₁ ∈ Formalism.HermitianLatticesTheory.isom h) (hg₂ : g₂ ∈ Formalism.HermitianLatticesTheory.isom h)
    (hx₁ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) (hx₂ : S.x₀ ∈ Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L))
    {J : ℕ} (hJ : 4 * vF 𝔭 n + eA h (locF 𝔭 L) 𝔭 + 1 ≤ J) {y : V}
    (h1 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₁.symm S.x₀))
    (h2 : y ∈ tube (autSub h (locF 𝔭 L)) (locF 𝔭 L) 𝔭 J (g₂.symm S.x₀)) :
    ∃ g' ∈ Formalism.HermitianLatticesTheory.isom h', Formalism.HermitianLatticesTheory.gmap (SplitBAux.extOf S g') (Formalism.HermitianLatticesTheory.gmap g₁ (locF 𝔭 L)) =
      Formalism.HermitianLatticesTheory.gmap g₂ (locF 𝔭 L) := by sorry
