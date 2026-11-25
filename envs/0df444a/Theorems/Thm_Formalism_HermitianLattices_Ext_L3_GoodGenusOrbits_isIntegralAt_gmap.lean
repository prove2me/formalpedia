-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GoodGenusOrbits_isIntegralAt_gmap
-- name    : Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.isIntegralAt_gmap
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:18:07.076992+00:00
-- url     : https://prove2.me/theorems/6ae952c7-ec68-4585-85d4-fb52ded56204
-- title:
--   Good Genus Orbits: is Integral At gmap
-- statement:
--   The Good Genus Orbits construction uses the is Integral At gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L77-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L77-L82

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralAtLocF
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms SplitBAux

theorem Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.isIntegralAt_gmap {𝔭 : Ideal (𝓞 F)} {g : V ≃ₗ[K] V} (hg : g ∈ Formalism.HermitianLatticesTheory.isom h)
    {T : Submodule (𝓞 K) V} (hT : IsIntegralAt 𝔭 h T) : IsIntegralAt 𝔭 h (Formalism.HermitianLatticesTheory.gmap g T) := by sorry
