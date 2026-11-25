-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GoodGenusOrbits_Good_of_genus
-- name    : Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.Good.of_genus
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:17:17.867827+00:00
-- url     : https://prove2.me/theorems/76b8acf9-6426-5159-a85e-49ecc535ef96
-- title:
--   Good: of genus
-- statement:
--   The Good construction uses the of genus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L122-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L122-L127

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

theorem Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.Good.of_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    {S : VecSplit h h'} {L : Submodule (𝓞 K) V} {M M₁ : Submodule (𝓞 K) V'}
    (hM : Good F S L M) (h1 : M₁ ∈ Formalism.HermitianLatticesTheory.genus h' M) : Good F S L M₁ := by sorry
