-- Prove2me | solution 1 for jankov_von_neumann
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:07:26.964075+00:00
-- url     : https://prove2.me/submissions/8d18c7e8-21a0-4b7a-8502-1345bda8a9cb

import Mathlib.Topology.MetricSpace.Polish
import Mathlib.Topology.MetricSpace.PiNat
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Definitions.Def_BicausalOT_DescriptiveSetTheory_AnalyticSigmaAlgebra
import Definitions.Def_BicausalOT_DescriptiveSetTheory_Tree
import Theorems.Thm_jvn_closedG
import Theorems.Thm_AnalyticallyMeasurable_comp_continuous


set_option autoImplicit false
open Set Topology MeasureTheory
open scoped Classical
noncomputable section
variable {X : Type*} [TopologicalSpace X]
theorem _root_.solution
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [PolishSpace X] [PolishSpace Y]
    (P : Set (X × Y)) (hP : AnalyticSet P) (hne : P.Nonempty) :
    ∃ (φ : X → Y), AnalyticallyMeasurable φ ∧
      ∀ x ∈ Prod.fst '' P, (x, φ x) ∈ P := by
  rw [AnalyticSet] at hP
  rcases hP with rfl | ⟨π, hπ_cont, hπ_range⟩
  · exact absurd hne (by simp)
  -- F = {(x, z) ∈ X × ℕᴺ | fst(π(z)) = x} is closed
  let F : Set (X × (ℕ → ℕ)) := { p | Prod.fst (π p.2) = p.1 }
  have hF_closed : IsClosed F :=
    isClosed_eq (hπ_cont.fst.comp continuous_snd) continuous_fst
  have hF_ne : F.Nonempty := by
    obtain ⟨⟨x, y⟩, hxy⟩ := hne
    obtain ⟨z, hz⟩ := (hπ_range ▸ hxy : (x, y) ∈ range π)
    exact ⟨(x, z), show Prod.fst (π z) = x from congr_arg Prod.fst hz⟩
  -- Apply generalized jvn_closed: get ψ : X → ℕᴺ
  obtain ⟨ψ, hψ_meas, hψ_sel⟩ := jvn_closedG hF_closed hF_ne
  -- φ(x) = snd(π(ψ(x)))
  refine ⟨fun x => Prod.snd (π (ψ x)),
    hψ_meas.comp_continuous (hπ_cont.snd.comp continuous_id), fun x hx => ?_⟩
  have hx_projF : x ∈ Prod.fst '' F := by
    obtain ⟨⟨a, b⟩, hab, rfl⟩ := hx
    obtain ⟨z, hz⟩ := (hπ_range ▸ hab : (a, b) ∈ range π)
    exact ⟨(a, z), show Prod.fst (π z) = a from congr_arg Prod.fst hz, rfl⟩
  have hfst : Prod.fst (π (ψ x)) = x := hψ_sel x hx_projF
  rw [show (x, Prod.snd (π (ψ x))) = π (ψ x) from Prod.ext hfst.symm rfl, ← hπ_range]
  exact mem_range_self _
