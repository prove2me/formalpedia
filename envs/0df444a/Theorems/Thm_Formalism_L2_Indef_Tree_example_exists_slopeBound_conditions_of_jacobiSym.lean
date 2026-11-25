-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_example_exists_slopeBound_conditions_of_jacobiSym
-- name    : Formalism.L2.Indef.Tree.example_exists_slopeBound_conditions_of_jacobiSym
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:51:32.606032+00:00
-- url     : https://prove2.me/theorems/9152d877-9c4d-4c7d-8fb6-70e45bb5e299
-- title:
--   Tree: example exists slope Bound conditions of jacobi Sym
-- statement:
--   The Tree construction uses the example exists slope Bound conditions of jacobi Sym property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L912-L938
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L912-L938

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

theorem Formalism.L2.Indef.Tree.example_exists_slopeBound_conditions_of_jacobiSym (v0 : InfinitePlace Examples₂.K3) (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n)
    (hχ : (∀ k : ℕ, χ k = ((jacobiSym k n : ℤ) : ℂ)) ∧ χ.IsPrimitive ∧ χ.Odd) (hper : PeriodIdentity n χ) :
    ∃ (P : SlopeBoundParameters) (F : (Examples₂.one.base Examples₂.K3 v0).J → SlopeBoundLiftData Examples₂.K3 P)
      (Zs : IndefScale (Examples₂.one.base Examples₂.K3 v0)),
      LeafKL P ∧ LeafCN P ∧ LeafFE P ∧ LeafDiff P ∧ LeafNorm P ∧ PageParams P ∧
      (∀ j, FacParams 0 (F j) ∧ LeafDegFlat 0 (F j) ∧ LeafExport 0 (F j) ∧ LeafCut (F j) ∧ LeafShareBad (F j) ∧
        LeafBadRows (F j) ∧ LeafMuN (F j) ∧ LeafLam (F j) ∧
        LeafRecord ((Examples₂.one.dat Examples₂.K3 v0).XW j) ((Examples₂.one.dat Examples₂.K3 v0).M j) (F j) ∧ LeafNote2 0 (F j) ∧
        LeafMeasure 0 (D := (Examples₂.one.dat Examples₂.K3 v0).D) ((Examples₂.one.dat Examples₂.K3 v0).XW j)
          ((Examples₂.one.dat Examples₂.K3 v0).XW j) ((Examples₂.one.dat Examples₂.K3 v0).M j) P ∧
        (F j).q' = 0 ∧ LeafDef 0 0 (F j)) ∧
      ScaleTies Zs P F := by sorry
