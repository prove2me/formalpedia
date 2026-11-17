-- Prove2me | solution 1 for thm_1_1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:26:07.523507+00:00
-- url     : https://prove2.me/submissions/347da538-b252-4664-925e-4c811c93e82c

import Definitions.Def_ProbabilityTheory_chapter_01_def_1_2_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F000
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_basic_F001
import Definitions.Def_ProbabilityTheory_chapter_01_thm_1_1_common_limit_F001
import Theorems.Thm_Thm11SourceRoute_strict_thm_1_1
import Mathlib.Data.List.GetD
import Mathlib.Tactic
import Mathlib.Topology.MetricSpace.Infsep
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Control.Monad.Cont


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Finset BigOperators
open Set Topology

noncomputable section

/-
Support entry for Theorem 1.1.

The proof body is split across:

- `thm_1_1_basic`
- `thm_1_1_oscillation_basic`
- `thm_1_1_bad_cells`
- `thm_1_1_Daboux_gap`
- `thm_1_1_common_refinement_point`
- `thm_1_1_common_refinement_monotonicity`
- `thm_1_1_finite_discontinuity`
- `thm_1_1_common_limit`
-/


theorem solution
    {f α : ℝ → ℝ} {a b : ℝ}
    (hab : a < b)
    (hα_mono : MonotoneOn α (Icc a b))
    (hAbove : BddAbove (f '' Icc a b))
    (hBelow : BddBelow (f '' Icc a b))
    (hDiscFinite : (discontinuitySetOn f a b).Finite)
    (hαCont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b →
      ContinuousWithinAt α (Icc a b) x) :
    RSIntegrable f α a b := by
  let clip : ℝ → ℝ := fun x => (Set.projIcc a b hab.le x : ℝ)
  let β : ℝ → ℝ := fun x => α (clip x)
  have hclip_mem : ∀ x : ℝ, clip x ∈ Icc a b := by
    intro x
    exact (Set.projIcc a b hab.le x).property
  have hclip_mono : Monotone clip := by
    intro x y hxy
    exact Set.monotone_projIcc hab.le hxy
  have hclip_cont : Continuous clip := by
    exact continuous_subtype_val.comp continuous_projIcc
  have hclip_eq : ∀ {x : ℝ}, x ∈ Icc a b → clip x = x := by
    intro x hx
    exact congrArg Subtype.val (Set.projIcc_of_mem hab.le hx)
  have hclip_maps : MapsTo clip Set.univ (Icc a b) := by
    intro x _hx
    exact hclip_mem x
  have hβ_mono : Monotone β := by
    intro x y hxy
    exact hα_mono (hclip_mem x) (hclip_mem y) (hclip_mono hxy)
  have hβ_eq : Set.EqOn β α (Icc a b) := by
    intro x hx
    simp only [β, hclip_eq hx]
  have hβ_cont : ∀ ⦃x : ℝ⦄, x ∈ discontinuitySetOn f a b →
      ContinuousAt β x := by
    intro x hx
    have hxI : x ∈ Icc a b := hx.1
    have hcomp : ContinuousWithinAt (α ∘ clip) Set.univ x :=
      (hαCont hx).comp_of_eq
        hclip_cont.continuousAt.continuousWithinAt hclip_maps (hclip_eq hxI)
    change ContinuousAt (α ∘ clip) x
    exact (continuousWithinAt_univ (α ∘ clip) x).mp hcomp
  have hβ : RSIntegrable f β a b :=
    Thm11SourceRoute.strict_thm_1_1
      hab hβ_mono hAbove hBelow hDiscFinite hβ_cont
  exact RSIntegrable.congr_integrator_on_Icc hβ_eq hβ