-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_GoodGenusOrbits_isClassReps_filter
-- name    : Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.isClassReps_filter
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T07:17:42.252846+00:00
-- url     : https://prove2.me/theorems/4450998e-ca6a-44d8-a15d-2fbf996efa2e
-- title:
--   Good Genus Orbits: is Class Reps filter
-- statement:
--   The Good Genus Orbits construction uses the is Class Reps filter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L184-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsIntegralLatOfForall.lean#L184-L206

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

theorem Formalism.HermitianLattices.Ext.L3.GoodGenusOrbits.isClassReps_filter (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M)
    [DecidablePred fun Λ' : Submodule (𝓞 K) V' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'] :
    Formalism.ThetaLiftIndependence.IsClassReps h' M (s'.filter fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ') := by sorry
