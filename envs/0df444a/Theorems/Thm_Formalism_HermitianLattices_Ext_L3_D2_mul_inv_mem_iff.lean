-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_D2_mul_inv_mem_iff
-- name    : Formalism.HermitianLattices.Ext.L3.D2.mul_inv_mem_iff
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T06:32:46.490197+00:00
-- url     : https://prove2.me/theorems/27a40403-4173-5545-bd6c-afd252525fab
-- title:
--   D2: mul inv mem iff
-- statement:
--   The D2 construction uses the mul inv mem iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexSSubInfEq.lean#L88-L110
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/RelIndexSSubInfEq.lean#L88-L110

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SurjectiveOfNondegenerate
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RelIndexSSubInfEq
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.D2
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]

theorem Formalism.HermitianLattices.Ext.L3.D2.mul_inv_mem_iff {h : V →ₗ⋆[K] V →ₗ[K] K} (hs : h.IsSymm) {A B : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {n : ℕ}
    {U W : V ≃ₗ[K] V} (hUA : U ∈ glSub A) (hUB : U ∈ glSub B) (hWA : W ∈ glSub A) (hWB : W ∈ glSub B) :
    U * W⁻¹ ∈ sSub h B 𝔭 n ⊓ glSub A ↔ IA.phi h U - IA.phi h W ∈ hermL B 𝔭 n := by sorry
