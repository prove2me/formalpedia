-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GoodGenusOrbits_fibLoc_gmap
-- name    : Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.fibLoc_gmap
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:03:47.980136+00:00
-- url     : https://prove2.me/theorems/e4f963f0-7d73-4714-9d51-db4b993f49a2
-- title:
--   Good Genus Orbits: fib Loc gmap
-- statement:
--   The Good Genus Orbits construction uses the fib Loc gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L22-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L22-L46

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

theorem Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.fibLoc_gmap (hs : h.IsSymm) (S : VecSplit h h') (L : Submodule (𝓞 K) V) (𝔭 : Ideal (𝓞 F))
    {g' : V' ≃ₗ[K] V'} (hg' : g' ∈ Formalism.HermitianLatticesTheory.isom h') (T : Submodule (𝓞 K) V') :
    fibLoc S L 𝔭 (Formalism.HermitianLatticesTheory.gmap g' T) = fibLoc S L 𝔭 T := by sorry
