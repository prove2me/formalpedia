-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormOneGroup_cond_iff
-- name    : Formalism.HermitianLattices.Ext.L3.NormOneGroup.cond_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:28.160197+00:00
-- url     : https://prove2.me/theorems/684e86ed-cfe8-4f6a-a1b9-c411c5bcbff2
-- title:
--   Norm One Group: cond iff
-- statement:
--   The Norm One Group construction uses the cond iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormOneMkIff.lean#L133-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormOneMkIff.lean#L133-L152

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SmulGenMemIff
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_NormOneMkIff
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.NormOneGroup
open Formalism.HermitianLattices.Ext.L3.ExtendedPrimeIdeals Formalism.HermitianLattices.Ext.L3.EndomorphismScalars
variable {K F : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F] [Algebra F K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V]
variable {L : Submodule (𝓞 K) V} {𝔭 : Ideal (𝓞 F)} {e : V} {h : V →ₗ⋆[K] V →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.NormOneGroup.cond_iff (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hv' : n ∉ 𝔭 ^ (v + 1)) (hvk : v ≤ k) (b : 𝓞 K) :
    (∀ x y x' y' : ↥L,
      (Submodule.Quotient.mk x' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk x) →
      (Submodule.Quotient.mk y' : Qk L 𝔭 k) =
        algebraMap (𝓞 K) (Module.End (𝓞 K) (Qk L 𝔭 k)) b (Submodule.Quotient.mk y) →
      CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V))) ↔
      conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v) := by sorry
