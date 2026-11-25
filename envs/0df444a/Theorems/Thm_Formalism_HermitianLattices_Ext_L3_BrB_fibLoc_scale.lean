-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_BrB_fibLoc_scale
-- name    : Formalism.HermitianLattices.Ext.L3.BrB.fibLoc_scale
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:15:00.916876+00:00
-- url     : https://prove2.me/theorems/28e5d724-2f01-4f10-9b3d-9dbef7da5b5c
-- title:
--   Br B: fib Loc scale
-- statement:
--   The Br B construction uses the fib Loc scale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L96-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/ExistsLocReps.lean#L96-L116

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_FinIntermediate
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_DualLattice
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLocReps
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.BrB
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.BrB.fibLoc_scale (S : VecSplit h h') (L : Submodule (𝓞 K) V) {𝔭 : Ideal (𝓞 F)}
    (h𝔭 : 𝔭.IsPrime) {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h) {t : 𝓞 F} (ht : t ∉ 𝔭)
    (hc : algebraMap (𝓞 K) K (algebraMap (𝓞 F) (𝓞 K) t) ≠ 0) (T : Submodule (𝓞 K) V') :
    fibLoc (scaleSplit S _ hc) (Formalism.HermitianLatticesTheory.gmap g L) 𝔭 T = fibLoc S L 𝔭 T := by sorry
