-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_descent_cut_lines
-- name    : Formalism.L2.Indef.Tree.descent_cut_lines
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T11:43:47.321416+00:00
-- url     : https://prove2.me/theorems/41f6cc25-a6e6-4baa-82a9-7cf0edb4f607
-- title:
--   Tree: descent cut lines
-- statement:
--   The Tree construction uses the descent cut lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L384-L428
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L384-L428

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefExample
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_IndefiniteTreeX
import Definitions.Def_Formalism_MeanHeightDescent_DivisionInequalityWithCovolume
import Definitions.Def_Formalism_MeanHeightDescent_CovolumeFullAssemblyWeighted
import Definitions.Def_Formalism_ThetaSupremumBounds_LiftOperatorBoundOfFockJet
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefiniteTree_SlopeBoundSingleLiftOfDefinitions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module NumberField Formalism.HN
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef Formalism.L2.Indef.Tree
attribute [instance] SlopeBoundParameters.fPl SlopeBoundParameters.dimNeZero
attribute [instance] SlopeBoundLiftData.fι SlopeBoundLiftData.nι

theorem Formalism.L2.Indef.Tree.descent_cut_lines (K V ι W κ V2 ι2 : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
    [DecidableEq ι] [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    [Fintype κ] [DecidableEq κ] [AddCommGroup V2] [Module K V2] [Module (𝓞 K) V2]
    [IsScalarTower (𝓞 K) K V2] [Fintype ι2] [DecidableEq ι2]
    (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (b' : Basis κ K W) (X' : InfinitePlace K → Matrix κ κ ℂ)
    (b2 : Basis ι2 K V2) (X2 : InfinitePlace K → Matrix ι2 ι2 ℂ)
    (hX : ∀ v, IsUnit (X v).det) (hX' : ∀ v, IsUnit (X' v).det) (hX2 : ∀ v, IsUnit (X2 v).det)
    (φ : V →ₗ[K] W) (A : Submodule (𝓞 K) V) (B : Submodule (𝓞 K) W)
    (N Mb : Submodule (𝓞 K) V2) (e : V2 →ₗ[K] V2) (g : ℕ) (P Λ : ℝ)
    (hA : A.FG) (hB : B.FG) (hN : N.FG) (hMb : Mb.FG) (hA0 : A ≠ ⊥) (hN0 : N ≠ ⊥)
    (hinj : Function.Injective φ) (hmap : A.map (φ.restrictScalars (𝓞 K)) ≤ B) (hht : htMap b X b' X' φ ≤ P)
    (hmuB : muDef b' X' B = muDef b2 X2 N) (hminB : muMinDef b' X' B = muMinDef b2 X2 N)
    (hrk : rkK A ≤ rkK B)
    (hspan : ∃ s : Set V2, s ⊆ (N : Set V2) ∧ (∀ x ∈ s, ∀ v, Formalism.HermitianLatticesTheory.normAt b2 X2 v x ≤ Real.exp Λ) ∧
        (N : Set V2) ⊆ (Submodule.span K s : Set V2))
    (hg : 1 ≤ g) (hee : e ∘ₗ e = e)
    (hsa : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b2 X2 v (e x) y = Formalism.HermitianLatticesTheory.majAt b2 X2 v x (e y))
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) (hNM : N ≤ Mb) :
    (0 : ℝ) < (rkK A : ℝ) ∧ (rkK A : ℝ) ≤ (rkK B : ℝ) ∧
    (rkK A : ℝ) * (muDef b X A - P) + ((rkK B : ℝ) - (rkK A : ℝ)) * (-(2 * Λ)) ≤ (rkK B : ℝ) * muDef b2 X2 N ∧
    (0 : ℝ) < (rkK N : ℝ) ∧
    (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (0 : ℝ) ≤ (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (rkK N : ℝ) * muDef b2 X2 N ≤
      (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) *
        muDef b2 X2 (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * (muMaxDef b2 X2 Mb + 2 * Real.log g) := by sorry
