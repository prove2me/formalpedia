-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_cut_lines
-- name    : Formalism.L2.Indef.Tree.cut_lines
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T03:52:02.651242+00:00
-- url     : https://prove2.me/theorems/121c2771-083a-44dd-b5f5-fe03ba10f450
-- title:
--   Tree: cut lines
-- statement:
--   The Tree construction uses the cut lines property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L430-L450
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L430-L450

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

theorem Formalism.L2.Indef.Tree.cut_lines (K V2 ι2 : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V2] [Module K V2] [Module (𝓞 K) V2] [IsScalarTower (𝓞 K) K V2] [Fintype ι2] [DecidableEq ι2]
    (b2 : Basis ι2 K V2) (X2 : InfinitePlace K → Matrix ι2 ι2 ℂ) (hX2 : ∀ v, IsUnit (X2 v).det)
    (N Mb : Submodule (𝓞 K) V2) (e : V2 →ₗ[K] V2) (g : ℕ)
    (hN : N.FG) (hMb : Mb.FG) (hN0 : N ≠ ⊥) (hg : 1 ≤ g) (hee : e ∘ₗ e = e)
    (hsa : ∀ v x y, Formalism.HermitianLatticesTheory.majAt b2 X2 v (e x) y = Formalism.HermitianLatticesTheory.majAt b2 X2 v x (e y))
    (hint : ∀ x ∈ N, (g : K) • e x ∈ N) (hNM : N ≤ Mb) :
    (0 : ℝ) < (rkK N : ℝ) ∧
    (rkK N : ℝ) = (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (0 : ℝ) ≤ (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) ∧
    (rkK N : ℝ) * muDef b2 X2 N ≤
      (rkK (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) : ℝ) *
        muDef b2 X2 (N ⊓ (LinearMap.range e).restrictScalars (𝓞 K)) +
      (rkK (N ⊓ (LinearMap.ker e).restrictScalars (𝓞 K)) : ℝ) * (muMaxDef b2 X2 Mb + 2 * Real.log g) := by sorry
