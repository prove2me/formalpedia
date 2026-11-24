-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_card_quot_inf_mul
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.card_quot_inf_mul
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T09:47:50.873683+00:00
-- url     : https://prove2.me/theorems/2f903c0c-5403-4d5b-9b2c-194c6435869e
-- title:
--   LIOrb: card quot inf mul
-- statement:
--   The LIOrb construction uses the card quot inf mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotInfNeZero.lean#L52-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/CardQuotInfNeZero.lean#L52-L75

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardEqRelIndex
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardQuotInfNeZero
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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.card_quot_inf_mul (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F)
    {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) (hd : IsTotPosDef h)
    {M₁ M₂ : Submodule (𝓞 K) V} (hM₁ : Submodule.IsLattice K M₁)
    (hM₁i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₁) (hM₂ : Submodule.IsLattice K M₂)
    (hM₂i : Formalism.HermitianLatticesTheory.IsIntegralLat h M₂) {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal) :
    Nat.card (↥(locF 𝔭 M₁) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₁)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₁) 𝔭 =
      Nat.card (↥(locF 𝔭 M₂) ⧸ (locF 𝔭 M₁ ⊓ locF 𝔭 M₂).submoduleOf (locF 𝔭 M₂)) *
        Ideal.absNorm 𝔭 ^ vd h (locF 𝔭 M₂) 𝔭 := by sorry
