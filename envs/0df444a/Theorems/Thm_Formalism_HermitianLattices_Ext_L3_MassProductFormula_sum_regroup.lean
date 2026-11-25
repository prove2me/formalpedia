-- Prove2me | Theorems.Thm_Formalism_HermitianLattices_Ext_L3_MassProductFormula_sum_regroup
-- name    : Formalism.HermitianLattices.Ext.L3.MassProductFormula.sum_regroup
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T07:17:47.078999+00:00
-- url     : https://prove2.me/theorems/83d705d7-9a05-566f-91d7-486ddfd1b33f
-- title:
--   Mass Product Formula: sum regroup
-- statement:
--   The Mass Product Formula construction uses the sum regroup property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumRegroup.lean#L20-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GL3MeanSquares/GenusMeanAsymptotics/UnimodularClassRepresentatives/SumRegroup.lean#L20-L101

import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_IsLatticeOfFibReps
import Definitions.Def_Formalism_GL3MeanSquares_GenusMeanAsymptotics_UnimodularClassRepresentatives_SumRegroup
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
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.Ext Formalism.HermitianLattices.Ext.L3 Formalism.HermitianLattices.Ext.L3.MassProductFormula
variable {K F V V' : Type} [Field K] [NumberField K] [StarRing K] [Field F] [NumberField F]
  [Algebra F K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V]
  [IsScalarTower (𝓞 K) K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
  [Module (𝓞 K) V'] [IsScalarTower (𝓞 K) K V']
variable {h : V →ₗ⋆[K] V →ₗ[K] K} {h' : V' →ₗ⋆[K] V' →ₗ[K] K}
open UnimodularLocalization GoodPrimeTerms GoodGenusOrbits LocalFactorEquality
open Classical

theorem Formalism.HermitianLattices.Ext.L3.MassProductFormula.sum_regroup (hK : Formalism.HermitianLatticesTheory.IsCMUnram K) (hF : IsFixF K F) (hs : h.IsSymm)
    (hd : IsTotPosDef h) (S : VecSplit h h') {L : Submodule (𝓞 K) V}
    (hL : Submodule.IsLattice K L) (hLi : Formalism.HermitianLatticesTheory.IsIntegralLat h L) {c : ℝ}
    (hc : MassConst K F (finrank K V - 1) c)
    {s' : Finset (Submodule (𝓞 K) V')} (hs' : IsFibReps S L s')
    {n : 𝓞 F} (hn : h S.x₀ S.x₀ = algebraMap F K (n : F))
    {A : Submodule (𝓞 K) V'} (hA : Submodule.IsLattice K A) (hAi : Formalism.HermitianLatticesTheory.IsIntegralLat h' A)
    (Z : Finset {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal})
    (hZL : ∀ 𝔭 ∉ Z, vd h L 𝔭.1 = 0) (hZn : ∀ 𝔭 ∉ Z, vF 𝔭.1 n = 0)
    (hZA : ∀ 𝔭 ∉ Z, vd h' A 𝔭.1 = 0)
    (s : {𝔭 : Ideal (𝓞 F) // 𝔭.IsMaximal} → Finset (Submodule (𝓞 K) V'))
    (hsr : ∀ 𝔭, IsLocReps S L 𝔭.1 (s 𝔭)) :
    ∑ Λ' ∈ s', (Nat.card (fibG S L Λ') : ℝ) / (Nat.card (Formalism.ThetaLiftIndependence.autL h' Λ') : ℝ) =
      c * ∏ 𝔭 ∈ Z, ∑ T ∈ s 𝔭, (fibLoc S L 𝔭.1 T : ℝ) * lamP h' T 𝔭.1 := by sorry
