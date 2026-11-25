-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_pair
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.pair
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:37:43.687311+00:00
-- url     : https://prove2.me/theorems/2491c8bf-c9be-5df2-9777-8da42afe40d7
-- title:
--   LIOrb: pair
-- statement:
--   The LIOrb construction uses the pair property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean#L255-L378
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/MemSmulTopIff.lean#L255-L378

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomCongr
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeVdLeOne
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_MemSmulTopIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LIOrb
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.pair (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) {n : 𝓞 F}
    (hn : n ≠ 0) {x : V} (hx : h x x = algebraMap F K (n : F)) (hx₁ : x ∈ locF 𝔭 M₁)
    (hx₂ : x ∈ locF 𝔭 M₂) :
    ∀ᶠ J in atTop, ∀ᶠ k in atTop,
      cnt h (locF 𝔭 M₁) 𝔭 k n (tube (autSub h (locF 𝔭 M₁)) (locF 𝔭 M₁) 𝔭 J x) *
          Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 *
          (autSub h (locF 𝔭 M₁)).relIndex (autSub h (locF 𝔭 M₂)) *
          (autSub h (locF 𝔭 M₂) ⊓ fixS x).relIndex (autSub h (locF 𝔭 M₁) ⊓ fixS x) =
        cnt h (locF 𝔭 M₂) 𝔭 k n (tube (autSub h (locF 𝔭 M₂)) (locF 𝔭 M₂) 𝔭 J x) *
          Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 *
          (autSub h (locF 𝔭 M₂)).relIndex (autSub h (locF 𝔭 M₁)) *
          (autSub h (locF 𝔭 M₁) ⊓ fixS x).relIndex (autSub h (locF 𝔭 M₂) ⊓ fixS x) := by sorry
