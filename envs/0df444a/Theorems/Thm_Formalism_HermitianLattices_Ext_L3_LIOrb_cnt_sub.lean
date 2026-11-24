-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_cnt_sub
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_sub
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T09:53:20.890808+00:00
-- url     : https://prove2.me/theorems/789726c0-1b3a-48f7-bda6-da2ab392a034
-- title:
--   LIOrb: cnt sub
-- statement:
--   The LIOrb construction uses the cnt sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L167-L273
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L167-L273

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SigmaCount
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NkCountLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsMulDvdUnif
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_FormRightMem
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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_sub (hF : IsFixF K F) {h : V →ₗ⋆[K] V →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    {A B : Submodule (𝓞 K) V} (hA : locF 𝔭 A = A) (hB : locF 𝔭 B = B)
    (hAi : IsIntegralAt 𝔭 h A) (hBA : B ≤ A) {k : ℕ}
    (hk : ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V) ≤ B)
    (hfin : Finite (↥B ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥B))) (n : 𝓞 F) {Ω : Set V}
    (hΩB : Ω ⊆ B) (hΩ : ∀ y ∈ Ω, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V), y + z ∈ Ω) :
    cnt h B 𝔭 k n Ω = Nat.card (↥A ⧸ B.submoduleOf A) * cnt h A 𝔭 k n Ω := by sorry
