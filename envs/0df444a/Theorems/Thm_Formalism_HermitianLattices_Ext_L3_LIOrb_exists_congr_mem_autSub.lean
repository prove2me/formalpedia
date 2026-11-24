-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_exists_congr_mem_autSub
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.exists_congr_mem_autSub
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T09:33:41.855672+00:00
-- url     : https://prove2.me/theorems/a5e65cce-1027-4770-be73-fadf672db2b8
-- title:
--   LIOrb: exists congr mem aut Sub
-- statement:
--   The LIOrb construction uses the exists congr mem aut Sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmulOfMemAutSub.lean#L129-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ApplyMemSmulOfMemAutSub.lean#L129-L148

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexEqOfCover
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ApplyMemSmulOfMemAutSub
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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.exists_congr_mem_autSub (h : V →ₗ⋆[K] V →ₗ[K] K) {M₁ M₂ : Submodule (𝓞 K) V}
    (hM₁ : Submodule.IsLattice K M₁) (hM₂ : Submodule.IsLattice K M₂) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsMaximal) :
    ∃ j₀ : ℕ, ∀ j, j₀ ≤ j → ∀ g ∈ autSub h (locF 𝔭 M₁),
      (∀ z ∈ locF 𝔭 M₁, g z - z ∈ ((extP K 𝔭) ^ j • locF 𝔭 M₁ : Submodule (𝓞 K) V)) →
      g ∈ autSub h (locF 𝔭 M₂) := by sorry
