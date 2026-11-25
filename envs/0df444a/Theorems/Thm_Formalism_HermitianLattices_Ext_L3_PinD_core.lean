-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_PinD_core
-- name    : Formalism.HermitianLattices.Ext.L3.PinD.core
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T09:23:33.732566+00:00
-- url     : https://prove2.me/theorems/71eb5ea8-5db8-5c9b-80b6-d235e53d7f70
-- title:
--   Pin D: core
-- statement:
--   The Pin D construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LiPin.lean#L20-L100
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/LiPin.lean#L20-L100

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_RepRatioEqZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsIsomLocFOfVdZero
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LamGEqOneOfOrtho
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsTotPosDefOfSmul
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_LiPin
import Theorems.Thm_Formalism_HermitianLattices_Ext_L3_WCC_core

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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3
open Formalism.HermitianLattices.Ext.L3.PinD
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}

theorem Formalism.HermitianLattices.Ext.L3.PinD.core (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (n : 𝓞 F) (hn : n ≠ 0)
    (S : VecSplit (algebraMap F K (n : F) • h) (algebraMap F K (n : F) • h'))
    (hs' : (algebraMap F K (n : F) • h).IsSymm) (hd' : IsTotPosDef (algebraMap F K (n : F) • h))
    {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsMaximal)
    (hx : (algebraMap F K (n : F) • h) S.x₀ S.x₀ = algebraMap F K (n : F)) :
    ∃ L₀ : Submodule (𝓞 K) V, Submodule.IsLattice K L₀ ∧
      Formalism.HermitianLatticesTheory.IsIntegralLat (algebraMap F K (n : F) • h) L₀ ∧
      repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n ≠ 0 ∧
      psiP S L₀ 𝔭 = (Ideal.absNorm 𝔭 : ℝ) ^ ((finrank K V - 1) * vF 𝔭 n) *
        alphaStd K 𝔭 (finrank K V - 1) * repRatio (algebraMap F K (n : F) • h) L₀ 𝔭 n := by sorry
