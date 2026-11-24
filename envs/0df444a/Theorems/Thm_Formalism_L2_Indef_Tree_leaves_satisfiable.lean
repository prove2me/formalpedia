-- Prove2me | Theorems.Thm_Formalism_L2_Indef_Tree_leaves_satisfiable
-- name    : Formalism.L2.Indef.Tree.leaves_satisfiable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:36:56.062027+00:00
-- url     : https://prove2.me/theorems/a14ae4d3-c8e9-4c31-86d3-49c370c30a7a
-- title:
--   Tree: leaves satisfiable
-- statement:
--   The Tree construction uses the leaves satisfiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L794-L903
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/IndefiniteTree/SlopeBoundSingleLiftOfDefinitions.lean#L794-L903

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

theorem Formalism.L2.Indef.Tree.leaves_satisfiable {K : Type} [Field K] [NumberField K] [StarRing K] {d D : ℕ}
    (XW : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (M : Submodule (𝓞 K) (Fin d → K))
    (hXW : ∀ v, IsUnit (XW v).det) (hMfg : M.FG) (hM0 : M ≠ ⊥)
    (n : ℕ) [NeZero n] (χ : DirichletCharacter ℂ n)
    (hχ : (∀ k : ℕ, χ k = ((jacobiSym k n : ℤ) : ℂ)) ∧ χ.IsPrimitive ∧ χ.Odd) (hper : PeriodIdentity n χ) :
    ∃ (P : SlopeBoundParameters) (F : SlopeBoundLiftData K P), LeafKL P ∧ LeafCN P ∧ LeafFE P ∧ LeafDiff P ∧ LeafNorm P ∧
      PageParams P ∧ FacParams 0 F ∧ LeafDegFlat 0 F ∧ LeafExport 0 F ∧ LeafCut F ∧ LeafShareBad F ∧
      LeafBadRows F ∧ LeafMuN F ∧ LeafLam F ∧ LeafRecord XW M F ∧ LeafNote2 0 F ∧
      LeafMeasure 0 (D := D) XW XW M P ∧ F.q' = 0 ∧ LeafDef 0 0 F ∧ P.m = 1 ∧
      F.pq = P.k + P.m - 1 - 2 * (F.q' : ℝ) := by sorry
