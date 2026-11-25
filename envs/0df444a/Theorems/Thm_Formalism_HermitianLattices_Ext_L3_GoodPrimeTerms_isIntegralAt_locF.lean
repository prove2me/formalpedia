-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GoodPrimeTerms_isIntegralAt_locF
-- name    : Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms.isIntegralAt_locF
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T06:32:41.087891+00:00
-- url     : https://prove2.me/theorems/404e9042-45cf-52c9-8f7a-4b2f3285ded1
-- title:
--   Good Prime Terms: is Integral At loc F
-- statement:
--   The Good Prime Terms construction uses the is Integral At loc F property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralAtLocF.lean#L48-L68
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralAtLocF.lean#L48-L68

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_ExistsLatticeOfFibLocNeZeroGood
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_CardFibGEqProd
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField Module Formalism.HermitianLattices.Ext.L3.SplitA
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization

theorem Formalism.HermitianLattices.Ext.L3.GoodPrimeTerms.isIntegralAt_locF {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] {h₀ : W →ₗ⋆[K] W →ₗ[K] K} {𝔭 : Ideal (𝓞 F)} (h𝔭 : 𝔭.IsPrime)
    (hF : IsFixF K F) {C : Submodule (𝓞 K) W}
    (hCi : Formalism.HermitianLatticesTheory.IsIntegralLat h₀ C) : IsIntegralAt 𝔭 h₀ (locF 𝔭 C) := by sorry
