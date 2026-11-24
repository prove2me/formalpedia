-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LIOrb_cnt_biUnion
-- name    : Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_biUnion
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T09:34:00.84891+00:00
-- url     : https://prove2.me/theorems/bf441773-991d-4637-a0e0-2fa8b72322df
-- title:
--   LIOrb: cnt bi Union
-- statement:
--   The LIOrb construction uses the cnt bi Union property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L67-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/FormRightMem.lean#L67-L100

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

theorem Formalism.HermitianLattices.Ext.L3.LIOrb.cnt_biUnion (h : V →ₗ⋆[K] V →ₗ[K] K) (A : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F)) (k : ℕ)
    (n : 𝓞 F) (hfin : Finite (↥A ⧸ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥A)))
    {ι : Type*} (s : Finset ι) (Ω : ι → Set V)
    (hst : ∀ i ∈ s, ∀ y ∈ Ω i, ∀ z ∈ ((extP K 𝔭) ^ k • A : Submodule (𝓞 K) V), y + z ∈ Ω i)
    (hdis : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Disjoint (Ω i) (Ω j)) :
    cnt h A 𝔭 k n (⋃ i ∈ s, Ω i) = ∑ i ∈ s, cnt h A 𝔭 k n (Ω i) := by sorry
