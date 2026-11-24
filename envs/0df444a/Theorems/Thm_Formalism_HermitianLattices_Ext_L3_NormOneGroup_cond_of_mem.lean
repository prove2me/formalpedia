-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_NormOneGroup_cond_of_mem
-- name    : Formalism.HermitianLattices.Ext.L3.NormOneGroup.cond_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T09:06:15.757856+00:00
-- url     : https://prove2.me/theorems/f63f78b3-2a38-4825-bfd2-b9e5393c0246
-- title:
--   Norm One Group: cond of mem
-- statement:
--   The Norm One Group construction uses the cond of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormOneMkIff.lean#L16-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/NormOneMkIff.lean#L16-L76

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

theorem Formalism.HermitianLattices.Ext.L3.NormOneGroup.cond_of_mem (hF : IsFixF K F) (hs : h.IsSymm) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    (h𝔭 : 𝔭.IsMaximal) (he : IsGen L 𝔭 e) {n : 𝓞 F} (hn : h e e = algebraMap F K (n : F))
    {v k : ℕ} (hv : n ∈ 𝔭 ^ v) (hvk : v ≤ k) {b : 𝓞 K}
    (hc : conjO K b * b - 1 ∈ extP K 𝔭 ^ (k - v)) (x y x' y' : ↥L)
    (hx : x' - b • x ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L))
    (hy : y' - b • y ∈ ((extP K 𝔭) ^ k • ⊤ : Submodule (𝓞 K) ↥L)) :
    CongrP 𝔭 k (h (x' : V) (y' : V)) (h (x : V) (y : V)) := by sorry
