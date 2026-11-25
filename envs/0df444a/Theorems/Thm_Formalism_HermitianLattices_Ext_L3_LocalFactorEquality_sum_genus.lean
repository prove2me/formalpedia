-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_LocalFactorEquality_sum_genus
-- name    : Formalism.HermitianLattices.Ext.L3.LocalFactorEquality.sum_genus
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:17:41.244777+00:00
-- url     : https://prove2.me/theorems/7a279b39-48a9-5894-8903-f782bab4ad80
-- title:
--   Local Factor Equality: sum genus
-- statement:
--   The Local Factor Equality construction uses the sum genus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLatticeOfFibReps.lean#L100-L151
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/IsLatticeOfFibReps.lean#L100-L151

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsIntegralLatOfForall
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_MassBasic
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.LocalFactorEquality
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits
open Classical

theorem Formalism.HermitianLattices.Ext.L3.LocalFactorEquality.sum_genus (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZ1 : ∀ 𝔭 ∉ Z, fibLoc S L 𝔭.1 A = 1) (hZ2 : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    {M : Submodule (𝓞 K) V'} (hM : Good F S L M) (hMA : ∀ 𝔭 ∉ Z, locF 𝔭.1 M = locF 𝔭.1 A) :
    ∑ Λ' ∈ s'.filter (fun Λ' => Formalism.HermitianLatticesTheory.SameGenus h' M Λ'),
        (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ((fibLoc S L 𝔭.1 (locF 𝔭.1 M) : ℝ) * lamP h' (locF 𝔭.1 M) 𝔭.1) := by sorry
